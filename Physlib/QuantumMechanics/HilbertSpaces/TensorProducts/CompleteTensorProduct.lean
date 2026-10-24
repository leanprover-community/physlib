/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philippe Kevorkian, Gregory J. Loges
-/
module

public import Mathlib.Analysis.InnerProductSpace.Completion
public import Mathlib.Analysis.InnerProductSpace.TensorProduct
public import Mathlib.Analysis.Normed.Operator.Extend
public import Physlib.Meta.TODO.Basic
/-!

# Complete tensor product

## i. Overview

Given two inner product spaces `E` and `F` over `𝕜`, their tensor product `E ⊗[𝕜] F` consists
of finite sums of simple (a.k.a. pure) tensors `m ⊗ₜ[𝕜] n`. This tensor product is again an inner
product space with inner product defined by `⟪m ⊗ₜ n, m' ⊗ₜ n'⟫_𝕜 = ⟪m, m'⟫_𝕜 * ⟪n, n'⟫_𝕜`
on simple tensors and then extended by linearity (c.f. `TensorProduct.instInnerProductSpace`).

However, in general this procedure does not result in a Hilbert space: Cauchy sequences need not
converge because the tensor product does not contain any _infinite_ sums of simple tensors.
In order to obtain a Hilbert space for use in quantum mechanics, we must _add in_ the limits
of Cauchy sequences by taking the completion.

In this module we define the complete tensor product,
`CompleteTensorProduct 𝕜 E F := Completion (E ⊗[𝕜] F)` with notation `E ⊗ₕ[𝕜] F` and `E ⊗ₕ F`,
provide some basic properties for the maps which embed `E ⊗[𝕜] F` into `E ⊗ₕ[𝕜] F`
and prove that `⊗ₕ` is commutative and associative (up to linear isometric equivalence).
We also construct the maps between complete tensor products induced by pairs of continuous
linear maps, of linear isometries and of linear isometric equivalences.

## ii. Key results

- `CompleteTensorProduct 𝕜 E F` (notation `E ⊗ₕ[𝕜] F` and `E ⊗ₕ F`) :
    The _completion_ of the tensor product of a pair of inner product spaces `E` and `F` over `𝕜`.
- `CompleteTensorProduct.comm 𝕜 E F` : The linear isometric equivalence between
    `E ⊗ₕ[𝕜] F` and `F ⊗ₕ[𝕜] E`.
- `CompleteTensorProduct.assoc 𝕜 E F G` : The linear isometric equivalence between
    `E ⊗ₕ[𝕜] F ⊗ₕ[𝕜] G` and `E ⊗ₕ[𝕜] (F ⊗ₕ[𝕜] G)`.
- `CompleteTensorProduct.assoc_tIncl₃ₗᵢ` : On the algebraic threefold tensor product,
    `CompleteTensorProduct.assoc` reduces to `TensorProduct.assoc`.
- `CompleteTensorProduct.mapLₕ f g` : The continuous linear map `E ⊗ₕ[𝕜] F →L[𝕜] G ⊗ₕ[𝕜] H`
    induced by `f : E →L[𝕜] G` and `g : F →L[𝕜] H`, of norm at most `‖f‖ * ‖g‖`.
- `CompleteTensorProduct.congrIsometryₕ f g` : The linear isometric equivalence
    `E ⊗ₕ[𝕜] F ≃ₗᵢ[𝕜] G ⊗ₕ[𝕜] H` induced by `f : E ≃ₗᵢ[𝕜] G` and `g : F ≃ₗᵢ[𝕜] H`.

## iii. Table of contents

- A. Definition
- B. Nontrivial
- C. Coercions
- D. Induction principle
- E. Commutative
- F. Associative
  - F.1. Associativity on the algebraic tensor product
- G. Induced maps

## iv. References

* None.
-/

@[expose] public section

noncomputable section

open UniformSpace
open scoped InnerProductSpace TensorProduct

/-!
## A. Definition
-/

/-- The _completion_ of the tensor product of two inner product spaces `E` and `F` over `𝕜`.
  By construction this produces a Hilbert space. The localized notations are `E ⊗ₕ F`
  and `E ⊗ₕ[𝕜] F`, accessed by `open scoped CompleteTensorProduct`. -/
def CompleteTensorProduct (𝕜 : Type*) [RCLike 𝕜]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (F : Type*) [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] : Type _ := Completion (E ⊗[𝕜] F)
deriving NormedAddCommGroup, InnerProductSpace 𝕜, CompleteSpace

@[inherit_doc CompleteTensorProduct]
scoped[CompleteTensorProduct] infixl:100 " ⊗ₕ " => CompleteTensorProduct _

@[inherit_doc]
scoped[CompleteTensorProduct]
notation:100 E:100 " ⊗ₕ[" 𝕜 "] " F:101 => CompleteTensorProduct 𝕜 E F

namespace CompleteTensorProduct

variable (𝕜 : Type*) [RCLike 𝕜]
variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable (F : Type*) [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-!
## B. Nontrivial
-/

section Nontrivial

variable [Nontrivial E] [Nontrivial F]

instance _root_.TensorProduct.instNontrivial : Nontrivial (E ⊗[𝕜] F) where
  exists_pair_ne := by
    obtain ⟨x, hx⟩ := exists_ne (0 : E)
    obtain ⟨y, hy⟩ := exists_ne (0 : F)
    exact ⟨x ⊗ₜ y, 0, norm_pos_iff.mp (by simp [hx, hy])⟩

instance instNontrivial : Nontrivial (E ⊗ₕ[𝕜] F) where
  exists_pair_ne := by
    obtain ⟨x, hx⟩ := exists_ne (0 : E ⊗[𝕜] F)
    exact ⟨Completion.coe' x, 0, fun h ↦ hx <| Completion.coe_eq_zero_iff.mp h⟩

end Nontrivial

/-!
## C. Coercions
-/

section Coercion

variable {𝕜 E F} (c : 𝕜) (x y : E ⊗[𝕜] F)

/-- The canonical embedding of the tensor product into its completion. -/
@[coe]
def coe' : E ⊗[𝕜] F → E ⊗ₕ[𝕜] F := Completion.coe'

/-- Coercion from `E ⊗[𝕜] F` to its completion. -/
instance : Coe (E ⊗[𝕜] F) (E ⊗ₕ[𝕜] F) := ⟨coe'⟩

lemma denseRange_coe : DenseRange (coe' : E ⊗[𝕜] F → E ⊗ₕ[𝕜] F) := Completion.denseRange_coe

@[norm_cast]
lemma coe_zero : (0 : E ⊗[𝕜] F) = (0 : E ⊗ₕ[𝕜] F) := rfl

variable {x} in
@[simp]
lemma coe_eq_zero_iff : (x : E ⊗ₕ[𝕜] F) = 0 ↔ x = 0 := Completion.coe_eq_zero_iff

@[norm_cast]
lemma coe_neg : (-x : E ⊗[𝕜] F) = (-x : E ⊗ₕ[𝕜] F) := Completion.coe_neg _

@[norm_cast]
lemma coe_sub : (x - y : E ⊗[𝕜] F) = (x - y : E ⊗ₕ[𝕜] F) := Completion.coe_sub _ _

@[norm_cast]
lemma coe_add : (x + y : E ⊗[𝕜] F) = (x + y : E ⊗ₕ[𝕜] F) := Completion.coe_add _ _

@[simp, norm_cast]
lemma coe_smul : (c • x : E ⊗[𝕜] F) = (c • x : E ⊗ₕ[𝕜] F) := Completion.coe_smul _ _

@[simp]
lemma inner_coe : ⟪(x : E ⊗ₕ[𝕜] F), (y : E ⊗ₕ[𝕜] F)⟫_𝕜 = ⟪x, y⟫_𝕜 := Completion.inner_coe _ _

@[simp]
lemma norm_coe : ‖(x : E ⊗ₕ[𝕜] F)‖ = ‖x‖ := Completion.norm_coe _

/-- The canonical embedding of the tensor product into its completion as a linear isometry. -/
def tInclₗᵢ : E ⊗[𝕜] F →ₗᵢ[𝕜] E ⊗ₕ[𝕜] F := Completion.toComplₗᵢ

@[simp]
lemma coe_tInclₗᵢ : ⇑(tInclₗᵢ : E ⊗ F →ₗᵢ[𝕜] E ⊗ₕ F) = coe' := rfl

/-- The canonical embedding of the tensor product into its completion as a continuous linear map. -/
def tInclL : E ⊗[𝕜] F →L[𝕜] E ⊗ₕ[𝕜] F := tInclₗᵢ.toContinuousLinearMap

@[simp]
lemma coe_tInclL : ⇑(tInclL : E ⊗ F →L[𝕜] E ⊗ₕ F) = coe' := rfl

@[simp]
lemma norm_tInclL [Nontrivial E] [Nontrivial F] : ‖(tInclL : E ⊗ F →L[𝕜] E ⊗ₕ F)‖ = 1 :=
  (tInclₗᵢ : E ⊗ F →ₗᵢ[𝕜] E ⊗ₕ F).norm_toContinuousLinearMap

end Coercion

/-!
## D. Induction principle
-/

section Induction

variable {𝕜 E F}

/-- An induction principle for `CompleteTensorProduct` combining those of `Completion`
  and `TensorProduct`. -/
@[elab_as_elim]
lemma induction_on {motive : E ⊗ₕ[𝕜] F → Prop} (z : E ⊗ₕ[𝕜] F)
    (tmul : ∀ (x : E) (y : F), motive (x ⊗ₜ[𝕜] y))
    (add : ∀ x y : E ⊗[𝕜] F, motive x → motive y → motive ↑(x + y))
    (closed : IsClosed {x | motive x}) : motive z :=
  Completion.induction_on z closed fun x ↦ x.inductionOn tmul add

end Induction

/-!
## E. Commutative
-/

section Commutative

/-- The complete tensor product of inner product spaces is commutative,
  up to linear isometric equivalence. -/
def comm : E ⊗ₕ[𝕜] F ≃ₗᵢ[𝕜] F ⊗ₕ[𝕜] E :=
  (TensorProduct.comm 𝕜 E F).extendOfIsometry tInclₗᵢ.toLinearMap tInclₗᵢ.toLinearMap
    denseRange_coe denseRange_coe (by simp)

@[simp]
lemma comm_symm : (comm 𝕜 E F).symm = comm 𝕜 F E := rfl

variable {𝕜 E F} in
@[simp]
lemma comm_coe (x : E ⊗[𝕜] F) : comm 𝕜 E F x = TensorProduct.comm 𝕜 E F x :=
  LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ _

end Commutative

/-!
## F. Associative
-/

section Associative

/-- The tensor product of a pair of linear maps with dense range also has dense range. -/
lemma _root_.TensorProduct.denseRange_map
    {R 𝕜 : Type*} [CommSemiring R] [RCLike 𝕜] {σ : R →+* 𝕜} [RingHomSurjective σ]
    {M : Type*} [AddCommMonoid M] [Module R M] {N : Type*} [AddCommMonoid N] [Module R N]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    {f : M →ₛₗ[σ] E} (hf : DenseRange f) {g : N →ₛₗ[σ] F} (hg : DenseRange g) :
    DenseRange (TensorProduct.map f g) := by
  intro x
  change x ∈ (TensorProduct.map f g).range.topologicalClosure
  refine x.inductionOn (fun a b ↦ ?_) (fun _ _ ↦ Submodule.add_mem _)
  refine map_mem_closure₂' (fun u ↦ ?_) (fun v ↦ ?_) (hf a) (hg b) ?_
  · refine Metric.continuous_iff.mpr fun v ε hε ↦ ⟨ε / (1 + ‖u‖), by positivity, fun s hs ↦ ?_⟩
    rw [dist_eq_norm, ← TensorProduct.tmul_sub, TensorProduct.norm_tmul] at *
    refine lt_of_le_of_lt (b := (1 + ‖u‖) * ‖s - v‖) ?_ ?_
    · exact mul_le_mul_of_nonneg_right (by norm_num) (norm_nonneg _)
    · exact (lt_div_iff₀' <| by positivity).mp hs
  · refine Metric.continuous_iff.mpr fun u ε hε ↦ ⟨ε / (1 + ‖v‖), by positivity, fun s hs ↦ ?_⟩
    rw [dist_eq_norm, ← TensorProduct.sub_tmul, TensorProduct.norm_tmul] at *
    refine lt_of_le_of_lt (b := ‖s - u‖ * (1 + ‖v‖)) ?_ ?_
    · exact mul_le_mul_of_nonneg_left (by norm_num) (norm_nonneg _)
    · exact (lt_div_iff₀ <| by positivity).mp hs
  · exact fun _ ⟨u, hu⟩ _ ⟨v, hv⟩ ↦ ⟨u ⊗ₜ v, by simp [hu, hv]⟩

variable (G : Type*) [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]

/-- The compete tensor product of inner product spaces is associative,
  up to linear isometric equivalence. -/
def assoc : E ⊗ₕ[𝕜] F ⊗ₕ[𝕜] G ≃ₗᵢ[𝕜] E ⊗ₕ[𝕜] (F ⊗ₕ[𝕜] G) :=
  (TensorProduct.assoc 𝕜 E F G).extendOfIsometry
    (tInclₗᵢ.comp (tInclₗᵢ.rTensor G)).toLinearMap (tInclₗᵢ.comp (tInclₗᵢ.lTensor E)).toLinearMap
    (by
      rw [LinearIsometry.coe_toLinearMap, LinearIsometry.coe_comp]
      refine DenseRange.comp denseRange_coe ?_ tInclₗᵢ.continuous
      exact TensorProduct.denseRange_map denseRange_coe denseRange_id)
    (by
      rw [LinearIsometry.coe_toLinearMap, LinearIsometry.coe_comp]
      refine DenseRange.comp denseRange_coe ?_ tInclₗᵢ.continuous
      exact TensorProduct.denseRange_map denseRange_id denseRange_coe)
    fun _ ↦ by simp only [LinearIsometry.norm_map', TensorProduct.norm_assoc]

/-!
### F.1. Associativity on the algebraic tensor product
-/

section ThreefoldInclusions

variable {𝕜 E F G}

/-- The embedding of the algebraic threefold tensor product `E ⊗[𝕜] F ⊗[𝕜] G` into the complete
  tensor product `E ⊗ₕ[𝕜] F ⊗ₕ[𝕜] G` as a linear isometry: `E ⊗[𝕜] F` is first embedded into
  `E ⊗ₕ[𝕜] F`, then `(E ⊗ₕ[𝕜] F) ⊗[𝕜] G` is embedded into its completion. -/
def tIncl₃ₗᵢ : E ⊗[𝕜] F ⊗[𝕜] G →ₗᵢ[𝕜] E ⊗ₕ[𝕜] F ⊗ₕ[𝕜] G :=
  tInclₗᵢ.comp (tInclₗᵢ.rTensor G)

/-- The embedding of the algebraic threefold tensor product `E ⊗[𝕜] (F ⊗[𝕜] G)` into the
  complete tensor product `E ⊗ₕ[𝕜] (F ⊗ₕ[𝕜] G)` as a linear isometry: `F ⊗[𝕜] G` is first
  embedded into `F ⊗ₕ[𝕜] G`, then `E ⊗[𝕜] (F ⊗ₕ[𝕜] G)` is embedded into its completion. -/
def tIncl₃'ₗᵢ : E ⊗[𝕜] (F ⊗[𝕜] G) →ₗᵢ[𝕜] E ⊗ₕ[𝕜] (F ⊗ₕ[𝕜] G) :=
  tInclₗᵢ.comp (tInclₗᵢ.lTensor E)

/-- On a simple tensor `x ⊗ₜ y ⊗ₜ z`, the embedding `tIncl₃ₗᵢ` is the nested coercion. -/
@[simp]
lemma tIncl₃ₗᵢ_tmul (x : E) (y : F) (z : G) :
    tIncl₃ₗᵢ (x ⊗ₜ[𝕜] y ⊗ₜ[𝕜] z) = (x ⊗ₜ[𝕜] y ⊗ₜ[𝕜] z : (E ⊗ₕ[𝕜] F) ⊗[𝕜] G) :=
  rfl

/-- On a simple tensor `x ⊗ₜ (y ⊗ₜ z)`, the embedding `tIncl₃'ₗᵢ` is the nested coercion. -/
@[simp]
lemma tIncl₃'ₗᵢ_tmul (x : E) (y : F) (z : G) :
    tIncl₃'ₗᵢ (x ⊗ₜ[𝕜] (y ⊗ₜ[𝕜] z)) = (x ⊗ₜ[𝕜] (y ⊗ₜ[𝕜] z) : E ⊗[𝕜] (F ⊗ₕ[𝕜] G)) :=
  rfl

/-- `CompleteTensorProduct.assoc` acting on an element of the algebraic threefold tensor product
  reduces to `TensorProduct.assoc`. -/
@[simp]
lemma assoc_tIncl₃ₗᵢ (x : E ⊗[𝕜] F ⊗[𝕜] G) :
    assoc 𝕜 E F G (tIncl₃ₗᵢ x) = tIncl₃'ₗᵢ (TensorProduct.assoc 𝕜 E F G x) :=
  LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ x

/-- The inverse of `CompleteTensorProduct.assoc` acting on an element of the algebraic threefold
  tensor product reduces to the inverse of `TensorProduct.assoc`. -/
@[simp]
lemma assoc_symm_tIncl₃'ₗᵢ (x : E ⊗[𝕜] (F ⊗[𝕜] G)) :
    (assoc 𝕜 E F G).symm (tIncl₃'ₗᵢ x) = tIncl₃ₗᵢ ((TensorProduct.assoc 𝕜 E F G).symm x) :=
  LinearEquiv.extendOfIsometry_symm_eq _ _ _ _ _ _ x

/-- `CompleteTensorProduct.assoc` on simple tensors (c.f. `TensorProduct.assoc_tmul`). -/
@[simp]
lemma assoc_tmul (x : E) (y : F) (z : G) :
    assoc 𝕜 E F G (x ⊗ₜ[𝕜] y ⊗ₜ[𝕜] z : (E ⊗ₕ[𝕜] F) ⊗[𝕜] G) =
      (x ⊗ₜ[𝕜] (y ⊗ₜ[𝕜] z) : E ⊗[𝕜] (F ⊗ₕ[𝕜] G)) :=
  assoc_tIncl₃ₗᵢ (x ⊗ₜ[𝕜] y ⊗ₜ[𝕜] z)

/-- The inverse of `CompleteTensorProduct.assoc` on simple tensors
  (c.f. `TensorProduct.assoc_symm_tmul`). -/
@[simp]
lemma assoc_symm_tmul (x : E) (y : F) (z : G) :
    (assoc 𝕜 E F G).symm (x ⊗ₜ[𝕜] (y ⊗ₜ[𝕜] z) : E ⊗[𝕜] (F ⊗ₕ[𝕜] G)) =
      (x ⊗ₜ[𝕜] y ⊗ₜ[𝕜] z : (E ⊗ₕ[𝕜] F) ⊗[𝕜] G) :=
  assoc_symm_tIncl₃'ₗᵢ (x ⊗ₜ[𝕜] (y ⊗ₜ[𝕜] z))

end ThreefoldInclusions

end Associative

/-!
## G. Induced maps
-/

section Maps

variable {𝕜 E F}
variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- The continuous linear map `E ⊗ₕ[𝕜] F →L[𝕜] G ⊗ₕ[𝕜] H` induced by a pair of continuous linear
  maps `f : E →L[𝕜] G` and `g : F →L[𝕜] H`: the extension of `TensorProduct.map f g` from the
  dense image of `E ⊗[𝕜] F` (c.f. `TensorProduct.mapL`). -/
def mapLₕ (f : E →L[𝕜] G) (g : F →L[𝕜] H) : E ⊗ₕ[𝕜] F →L[𝕜] G ⊗ₕ[𝕜] H :=
  (tInclₗᵢ.toLinearMap ∘ₗ TensorProduct.map f.toLinearMap g.toLinearMap).extendOfNorm
    tInclₗᵢ.toLinearMap

/-- The linear isometry `E ⊗ₕ[𝕜] F →ₗᵢ[𝕜] G ⊗ₕ[𝕜] H` induced by a pair of linear isometries
  `f : E →ₗᵢ[𝕜] G` and `g : F →ₗᵢ[𝕜] H` (c.f. `TensorProduct.mapIsometry`). -/
def mapIsometryₕ (f : E →ₗᵢ[𝕜] G) (g : F →ₗᵢ[𝕜] H) : E ⊗ₕ[𝕜] F →ₗᵢ[𝕜] G ⊗ₕ[𝕜] H :=
  (tInclₗᵢ.comp (TensorProduct.mapIsometry f g)).toLinearMap.extendOfIsometry
    (e := tInclₗᵢ.toLinearMap) denseRange_coe fun _ ↦ by
      simp only [LinearIsometry.coe_toLinearMap, LinearIsometry.norm_map]

/-- The linear isometric equivalence `E ⊗ₕ[𝕜] F ≃ₗᵢ[𝕜] G ⊗ₕ[𝕜] H` induced by a pair of linear
  isometric equivalences `f : E ≃ₗᵢ[𝕜] G` and `g : F ≃ₗᵢ[𝕜] H`
  (c.f. `TensorProduct.congrIsometry`). -/
def congrIsometryₕ (f : E ≃ₗᵢ[𝕜] G) (g : F ≃ₗᵢ[𝕜] H) : E ⊗ₕ[𝕜] F ≃ₗᵢ[𝕜] G ⊗ₕ[𝕜] H :=
  (TensorProduct.congrIsometry f g).toLinearEquiv.extendOfIsometry tInclₗᵢ.toLinearMap
    tInclₗᵢ.toLinearMap denseRange_coe denseRange_coe fun _ ↦ by
      simp only [LinearIsometry.coe_toLinearMap, LinearIsometry.norm_map,
        LinearIsometryEquiv.coe_toLinearEquiv, LinearIsometryEquiv.norm_map]

/-- The bound `‖TensorProduct.map f g x‖ ≤ ‖f‖ * ‖g‖ * ‖x‖`, in the form used to extend
  `TensorProduct.map f g` to the complete tensor product. -/
private lemma norm_tInclₗᵢ_map_le (f : E →L[𝕜] G) (g : F →L[𝕜] H) (x : E ⊗[𝕜] F) :
    ‖(tInclₗᵢ.toLinearMap ∘ₗ TensorProduct.map f.toLinearMap g.toLinearMap) x‖ ≤
      ‖f‖ * ‖g‖ * ‖tInclₗᵢ.toLinearMap x‖ := by
  simpa only [LinearMap.comp_apply, LinearIsometry.coe_toLinearMap, LinearIsometry.norm_map,
    TensorProduct.mapL_apply] using
    (TensorProduct.mapL f g).le_of_opNorm_le (TensorProduct.norm_mapL_le f g) x

/-- On the image of an element of the algebraic tensor product, `mapLₕ f g` is
  `TensorProduct.map f g`. -/
@[simp]
lemma mapLₕ_coe (f : E →L[𝕜] G) (g : F →L[𝕜] H) (x : E ⊗[𝕜] F) :
    mapLₕ f g x = TensorProduct.map f.toLinearMap g.toLinearMap x :=
  LinearMap.extendOfNorm_eq denseRange_coe ⟨_, norm_tInclₗᵢ_map_le f g⟩ x

/-- `mapLₕ f g` on simple tensors (c.f. `TensorProduct.mapL_tmul`). -/
lemma mapLₕ_tmul (f : E →L[𝕜] G) (g : F →L[𝕜] H) (x : E) (y : F) :
    mapLₕ f g ((x ⊗ₜ[𝕜] y : E ⊗[𝕜] F) : E ⊗ₕ[𝕜] F) =
      ((f x ⊗ₜ[𝕜] g y : G ⊗[𝕜] H) : G ⊗ₕ[𝕜] H) :=
  mapLₕ_coe f g (x ⊗ₜ[𝕜] y)

/-- The operator norm of `mapLₕ f g` is at most `‖f‖ * ‖g‖`
  (c.f. `TensorProduct.norm_mapL_le`). -/
lemma norm_mapLₕ_le (f : E →L[𝕜] G) (g : F →L[𝕜] H) : ‖mapLₕ f g‖ ≤ ‖f‖ * ‖g‖ :=
  LinearMap.opNorm_extendOfNorm_le denseRange_coe (by positivity) (norm_tInclₗᵢ_map_le f g)

/-- On the image of an element of the algebraic tensor product, `mapIsometryₕ f g` is
  `TensorProduct.map f g` (c.f. `TensorProduct.mapIsometry_apply`). -/
@[simp]
lemma mapIsometryₕ_coe (f : E →ₗᵢ[𝕜] G) (g : F →ₗᵢ[𝕜] H) (x : E ⊗[𝕜] F) :
    mapIsometryₕ f g x = TensorProduct.map f.toLinearMap g.toLinearMap x :=
  LinearMap.extendOfIsometry_eq _ _ _ x

/-- The continuous linear map underlying `mapIsometryₕ f g` is `mapLₕ f g`
  (c.f. `TensorProduct.toContinuousLinearMap_mapIsometry`). -/
@[simp]
lemma toContinuousLinearMap_mapIsometryₕ (f : E →ₗᵢ[𝕜] G) (g : F →ₗᵢ[𝕜] H) :
    (mapIsometryₕ f g).toContinuousLinearMap =
      mapLₕ f.toContinuousLinearMap g.toContinuousLinearMap :=
  rfl

/-- On the image of an element of the algebraic tensor product, `congrIsometryₕ f g` is
  `TensorProduct.congr f g` (c.f. `TensorProduct.congrIsometry_apply`). -/
@[simp]
lemma congrIsometryₕ_coe (f : E ≃ₗᵢ[𝕜] G) (g : F ≃ₗᵢ[𝕜] H) (x : E ⊗[𝕜] F) :
    congrIsometryₕ f g x = TensorProduct.congr f.toLinearEquiv g.toLinearEquiv x :=
  LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ x

/-- The inverse of `congrIsometryₕ f g` is `congrIsometryₕ f.symm g.symm`
  (c.f. `TensorProduct.congrIsometry_symm`). -/
@[simp]
lemma congrIsometryₕ_symm (f : E ≃ₗᵢ[𝕜] G) (g : F ≃ₗᵢ[𝕜] H) :
    (congrIsometryₕ f g).symm = congrIsometryₕ f.symm g.symm :=
  rfl

/-- The linear isometry underlying `congrIsometryₕ f g` is `mapIsometryₕ f g`. -/
@[simp]
lemma toLinearIsometry_congrIsometryₕ (f : E ≃ₗᵢ[𝕜] G) (g : F ≃ₗᵢ[𝕜] H) :
    (congrIsometryₕ f g).toLinearIsometry =
      mapIsometryₕ f.toLinearIsometry g.toLinearIsometry :=
  rfl

end Maps

TODO "Define LinearPMap.lTensor/rTensor, TensorProduct.mapP (P = 'partial'?) for the tensor product.
  See LinearMap/LinearEquiv/ContinuousLinearMap/LinearIsometry/LinearIsometryEquiv.lTensor/rTensor
  and TensorProduct.map/congr/mapL/mapIsometry/congrIsometry for the desired pattern. The tensor
  product of two LinearPMaps f and g is the canonical LinearPMap with domain f.domain ⊗ g.domain."

TODO "Define CompleteTensorProduct.mapPₕ/congrLₕ/etc. (or a different naming scheme) which take
  pairs of partial/etc. maps or of continuous linear equivalences and construct the
  corresponding map/congruence on complete tensor products (c.f. TensorProduct.congrL, and the
  TODO above for TensorProduct.mapP). Pairs of continuous linear maps, of linear isometries and
  of linear isometric equivalences are handled by mapLₕ, mapIsometryₕ and congrIsometryₕ."

end CompleteTensorProduct
end
