/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Pseudo-inner product spaces

`PseudoInnerProductSpace E` equips a real topological vector space with a continuous symmetric
nondegenerate bilinear form. Dropping positivity leaves the topology of `E` free, so the class
attaches to a space that already carries one — a tangent space, a bundle fibre — without a
diamond. Inheritance runs `InnerProductSpace ℝ E → PseudoInnerProductSpace E`, never the reverse.

## Main definitions

* `PseudoInnerProductSpace E`: the class; `pseudoInner v w` is its scalar pairing and
  `PseudoInnerProductSpace.flatL` the same pairing as a continuous linear map.
* `PseudoInnerProductSpace.ofBilinForm`: build the structure from a symmetric nondegenerate
  bilinear form on a finite-dimensional Hausdorff space.
* `PseudoInnerProductSpace.flatEquiv`, `sharpEquiv`, `sharpL`: `♭ : E ≃L[ℝ] E⋆` and its inverse.
* `PseudoInnerProductSpace.dualPseudoInnerSL`: the induced form on `E⋆`, the inverse metric.

## Implementation notes

The musical isomorphisms are linear algebra, so they serve tangent, normal and gauge bundles
alike. `♭` comes from `LinearMap.BilinForm.toDual`, hence is an isomorphism only under
`[T2Space E]` and `[FiniteDimensional ℝ E]`. Requiring instead that `♭` be an isomorphism outright
would restrict the `InnerProductSpace` instance to Hilbert spaces, since Fréchet-Riesz needs
completeness, and so would defeat the subsumption.

The pairing is separately, not jointly, continuous: it is a continuous linear map into a space of
continuous linear maps. That is what `InnerProductSpace` supplies for free, and it is why the form
is not registered as a `LinearMap.IsContPerfPair`, which requires joint continuity.

## Acknowledgements

The design follows Sébastien Gouëzel's proposal — a fibrewise class for the bilinear form, an
instance from `InnerProductSpace`, and a weakening of `IsContMDiffRiemannianBundle` to it. See
[Zulip](https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/The.20future.20of.20pseudo-Riemannian.20manifolds/with/619509253).

## Tags

pseudo-inner product, nondegenerate bilinear form, musical isomorphism, index raising
-/

@[expose] public section

open Module

/-! ## The quadratic form of a continuous bilinear form -/

namespace ContinuousLinearMap

variable {𝕜 E : Type*} [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]

/-- The quadratic form `v ↦ B v v` of a continuous bilinear form. No symmetry is required: the
companion is `(v, w) ↦ B v w + B w v`. -/
def toQuadraticForm (B : E →L[𝕜] E →L[𝕜] 𝕜) : QuadraticForm 𝕜 E := B.toBilinForm.toQuadraticMap

@[simp]
lemma toQuadraticForm_apply (B : E →L[𝕜] E →L[𝕜] 𝕜) (v : E) : B.toQuadraticForm v = B v v := rfl

end ContinuousLinearMap

/-! ## The class -/

/-- A real topological vector space with a continuous symmetric nondegenerate bilinear form.
Positivity is not assumed, so the topology of `E` is independent data.

`Pseudo` weakens positive definiteness to nondegeneracy, as in "pseudo-Riemannian"; definite forms
are the index-`0` special case rather than being excluded. This is not the usual Mathlib sense of
dropping a separation axiom. -/
class PseudoInnerProductSpace (E : Type*) [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] where
  /-- The pseudo-inner product, as a continuous bilinear map. -/
  pseudoInnerSL : E →L[ℝ] E →L[ℝ] ℝ
  /-- The pseudo-inner product is symmetric. -/
  pseudoInner_symm : ∀ v w : E, pseudoInnerSL v w = pseudoInnerSL w v
  /-- The pseudo-inner product is nondegenerate: a vector pairing to zero with everything is
  itself zero. -/
  pseudoInner_nondegenerate : ∀ v : E, (∀ w : E, pseudoInnerSL v w = 0) → v = 0

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]

/-- The pseudo-inner product `⟪v, w⟫` of two vectors of a pseudo-inner product space. -/
noncomputable def pseudoInner [PseudoInnerProductSpace E] (v w : E) : ℝ :=
  PseudoInnerProductSpace.pseudoInnerSL v w

namespace PseudoInnerProductSpace

section Basic

variable [PseudoInnerProductSpace E]

lemma pseudoInner_comm (v w : E) : pseudoInner v w = pseudoInner w v :=
  pseudoInner_symm v w

lemma eq_zero_of_pseudoInner_eq_zero {v : E} (h : ∀ w : E, pseudoInner v w = 0) : v = 0 :=
  pseudoInner_nondegenerate v h

lemma eq_zero_of_pseudoInner_right_eq_zero {w : E} (h : ∀ v : E, pseudoInner v w = 0) : w = 0 :=
  pseudoInner_nondegenerate w fun v ↦ (pseudoInner_comm w v).trans (h v)

@[simp] lemma pseudoInner_zero_left (w : E) : pseudoInner (0 : E) w = 0 :=
  congrFun (congrArg _ (map_zero (pseudoInnerSL (E := E)))) w

@[simp] lemma pseudoInner_zero_right (v : E) : pseudoInner v (0 : E) = 0 :=
  map_zero (pseudoInnerSL v)

lemma pseudoInner_add_left (u v w : E) :
    pseudoInner (u + v) w = pseudoInner u w + pseudoInner v w :=
  congrFun (congrArg _ (map_add (pseudoInnerSL (E := E)) u v)) w

lemma pseudoInner_add_right (u v w : E) :
    pseudoInner u (v + w) = pseudoInner u v + pseudoInner u w :=
  map_add (pseudoInnerSL u) v w

lemma pseudoInner_sub_left (u v w : E) :
    pseudoInner (u - v) w = pseudoInner u w - pseudoInner v w :=
  congrFun (congrArg _ (map_sub (pseudoInnerSL (E := E)) u v)) w

lemma pseudoInner_sub_right (u v w : E) :
    pseudoInner u (v - w) = pseudoInner u v - pseudoInner u w :=
  map_sub (pseudoInnerSL u) v w

lemma pseudoInner_smul_left (c : ℝ) (v w : E) :
    pseudoInner (c • v) w = c * pseudoInner v w :=
  congrFun (congrArg _ (map_smul (pseudoInnerSL (E := E)) c v)) w

lemma pseudoInner_smul_right (c : ℝ) (v w : E) :
    pseudoInner v (c • w) = c * pseudoInner v w :=
  map_smul (pseudoInnerSL v) c w

/-- The algebraic content of the uniqueness of the Levi-Civita connection: a map symmetric in its
two arguments and antisymmetric against the form in its outer arguments vanishes. Only symmetry
and nondegeneracy are used, so the statement is insensitive to signature. -/
lemma eq_zero_of_symm_of_antisymm {S : E → E → E} (hsymm : ∀ u v, S u v = S v u)
    (hanti : ∀ u v w, pseudoInner (S u v) w = -pseudoInner (S w v) u) (u v : E) :
    S u v = 0 := by
  refine eq_zero_of_pseudoInner_eq_zero fun w ↦ ?_
  have h1 := hanti u v w
  have h2 : pseudoInner (S w v) u = pseudoInner (S v w) u := by rw [hsymm w v]
  have h3 := hanti v w u
  have h4 : pseudoInner (S u w) v = pseudoInner (S w u) v := by rw [hsymm u w]
  have h5 := hanti w u v
  have h6 : pseudoInner (S v u) w = pseudoInner (S u v) w := by rw [hsymm v u]
  linarith

end Basic

/-! ## Riemannian geometry as a special case -/

section InnerProduct

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Every real inner product space is a pseudo-inner product space: positive definiteness is in
particular nondegeneracy. This instance is what makes the subsumption automatic. -/
noncomputable instance (priority := 100) _root_.InnerProductSpace.toPseudoInnerProductSpace :
    PseudoInnerProductSpace F where
  pseudoInnerSL := innerSL ℝ
  pseudoInner_symm v w := real_inner_comm w v
  pseudoInner_nondegenerate v hv := (inner_self_eq_zero (𝕜 := ℝ)).mp (hv v)

@[simp]
lemma pseudoInner_eq_inner (v w : F) : pseudoInner v w = inner ℝ v w := rfl

end InnerProduct

/-! ## The associated bilinear and quadratic forms -/

section Forms

variable [PseudoInnerProductSpace E]

variable (E) in
/-- Index lowering `♭ : v ↦ pseudoInner v ·`, definitionally the pseudo-inner product.

A `def` rather than an `abbrev`: a reducible `flatL` would give `flatL_apply` the same left-hand
side as the unfolding of `pseudoInner`, and any simp set containing `pseudoInner` would loop. -/
def flatL : E →L[ℝ] (E →L[ℝ] ℝ) := PseudoInnerProductSpace.pseudoInnerSL

@[simp]
lemma flatL_apply (v w : E) : flatL E v w = pseudoInner v w := rfl

lemma toBilinForm_isSymm : (flatL E).toBilinForm.IsSymm :=
  ⟨fun v w ↦ by simpa using (pseudoInner_comm v w)⟩

lemma toBilinForm_nondegenerate : (flatL E).toBilinForm.Nondegenerate :=
  ⟨fun v hv ↦ eq_zero_of_pseudoInner_eq_zero fun w ↦ by simpa using hv w,
    fun w hw ↦ eq_zero_of_pseudoInner_right_eq_zero fun v ↦ by simpa using hw v⟩

variable (E) in
/-- The quadratic form `v ↦ pseudoInner v v`. Its `QuadraticForm.sigNeg` is the index. -/
noncomputable def toQuadraticForm : QuadraticForm ℝ E := (flatL E).toQuadraticForm

@[simp]
lemma toQuadraticForm_apply (v : E) : toQuadraticForm E v = pseudoInner v v := rfl

end Forms

/-! ## Building an instance from a bilinear form -/

section OfBilinForm

variable (E) in
/-- Build a pseudo-inner product from a symmetric nondegenerate bilinear form on a
finite-dimensional Hausdorff space, where continuity is automatic. This is how a concrete metric
(Minkowski, Schwarzschild, FLRW) is supplied. -/
@[reducible] noncomputable def ofBilinForm [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [T2Space E] [FiniteDimensional ℝ E] (B : LinearMap.BilinForm ℝ E) (hs : B.IsSymm)
    (hn : B.Nondegenerate) : PseudoInnerProductSpace E where
  pseudoInnerSL := LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := E) (F' := ℝ)).toLinearMap ∘ₗ B)
  pseudoInner_symm := LinearMap.BilinForm.isSymm_def.mp hs
  pseudoInner_nondegenerate := hn.1

end OfBilinForm

/-! ## Musical isomorphisms -/

section Musical

variable [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
  [FiniteDimensional ℝ E] [PseudoInnerProductSpace E]

variable (E) in
/-- The musical isomorphism `♭ : E ≃L[ℝ] E⋆`, from `LinearMap.BilinForm.toDual` composed with the
identification of the algebraic and continuous duals in finite dimension. -/
noncomputable def flatEquiv : E ≃L[ℝ] (E →L[ℝ] ℝ) :=
  LinearEquiv.toContinuousLinearEquiv
    (((flatL E).toBilinForm.toDual toBilinForm_nondegenerate).trans
      (LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := E) (F' := ℝ)))

@[simp]
lemma flatEquiv_apply (v w : E) : flatEquiv E v w = pseudoInner v w := rfl

variable (E) in
/-- The musical isomorphism `♯ : E⋆ ≃L[ℝ] E`, inverse to `♭`. -/
noncomputable def sharpEquiv : (E →L[ℝ] ℝ) ≃L[ℝ] E := (flatEquiv E).symm

variable (E) in
/-- Index raising `♯ : E⋆ →L[ℝ] E`, as a continuous linear map. -/
noncomputable def sharpL : (E →L[ℝ] ℝ) →L[ℝ] E := (sharpEquiv E).toContinuousLinearMap

@[simp]
lemma sharpL_flatL (v : E) : sharpL E (flatL E v) = v :=
  (flatEquiv E).symm_apply_apply v

@[simp]
lemma flatL_sharpL (η : E →L[ℝ] ℝ) : flatL E (sharpL E η) = η :=
  (flatEquiv E).apply_symm_apply η

@[simp]
lemma pseudoInner_sharpL_right (v : E) (η : E →L[ℝ] ℝ) : pseudoInner v (sharpL E η) = η v := by
  rw [pseudoInner_comm, ← flatL_apply, flatL_sharpL]

@[simp]
lemma pseudoInner_sharpL_left (v : E) (η : E →L[ℝ] ℝ) : pseudoInner (sharpL E η) v = η v := by
  rw [pseudoInner_comm]; exact pseudoInner_sharpL_right v η

/-! ### The induced form on the dual -/

variable (E) in
/-- The form induced on `E⋆` by raising both indices, `(η₁, η₂) ↦ η₁ (η₂♯)`; for a metric tensor,
the inverse metric `g^{ab}`. -/
noncomputable def dualPseudoInnerSL : (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.precomp ℝ (sharpL E)

@[simp]
lemma dualPseudoInnerSL_apply (η₁ η₂ : E →L[ℝ] ℝ) :
    dualPseudoInnerSL E η₁ η₂ = η₁ (sharpL E η₂) := rfl

lemma dualPseudoInnerSL_eq_pseudoInner_sharpL (η₁ η₂ : E →L[ℝ] ℝ) :
    dualPseudoInnerSL E η₁ η₂ = pseudoInner (sharpL E η₁) (sharpL E η₂) := by
  rw [dualPseudoInnerSL_apply, pseudoInner_sharpL_left]

lemma dualPseudoInnerSL_symm (η₁ η₂ : E →L[ℝ] ℝ) :
    dualPseudoInnerSL E η₁ η₂ = dualPseudoInnerSL E η₂ η₁ := by
  simp only [dualPseudoInnerSL_eq_pseudoInner_sharpL]
  exact pseudoInner_comm _ _

lemma dualPseudoInnerSL_nondegenerate (η : E →L[ℝ] ℝ)
    (h : ∀ η' : E →L[ℝ] ℝ, dualPseudoInnerSL E η η' = 0) : η = 0 := by
  ext v
  simpa only [dualPseudoInnerSL_apply, sharpL_flatL, zero_apply]
    using h (flatL E v)

variable (E) in
/-- `E⋆` with the inverse form. Deliberately a `def`: as an instance it would let typeclass
inference loop through iterated duals. -/
@[reducible] noncomputable def dual : PseudoInnerProductSpace (E →L[ℝ] ℝ) where
  pseudoInnerSL := dualPseudoInnerSL E
  pseudoInner_symm := dualPseudoInnerSL_symm
  pseudoInner_nondegenerate := dualPseudoInnerSL_nondegenerate

end Musical

end PseudoInnerProductSpace
