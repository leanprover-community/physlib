/-
Copyright (c) 2026 Hirotaka Monya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hirotaka Monya
-/
module

public import Physlib.Units.WithDim.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Equiv
public import Mathlib.Analysis.Normed.Group.Basic

/-!
# A. Analysis of dimension-tagged quantities

The numerical value of `WithDim d M` identifies it with `M`. We use that explicit
identification to induce a norm on the existing additive group, not to replace
its addition, natural/integer scalar multiplication, or the existing `NNReal` action.

The norm measures a numerical representation in fixed units. It is not asserted to
be invariant under a change of units. The coordinate equivalence is explicit: no
coercion silently discards a dimension tag. No `Ring` or `Field` on a nontrivial
physical dimension is introduced.

`transport` and `transportLinearMap` lift a function and its derivative between tagged
coordinates. They do not assert that the function is dimensionally correct. In particular,
changing the units of model parameters is a separate question. `hasFDerivAt_transport`
uses the existing calculus of continuous linear equivalences.
-/

@[expose] public section

noncomputable section

namespace WithDim

variable {B : Type} [DimensionBasis B]

/-!
## A.1. Coordinates and the induced norm
-/

/-- Forget the dimension tag by an explicit additive equivalence of numerical values. -/
def toValueAddEquiv (d : Dimension B) (M : Type) [AddCommMonoid M] :
    WithDim d M ≃+ M where
  toFun := WithDim.val
  invFun x := ⟨x⟩
  left_inv x := by cases x; rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- The existing additive group carries the norm of its numerical representation. -/
instance instNormedAddCommGroup (d : Dimension B) (M : Type) [NormedAddCommGroup M] :
    NormedAddCommGroup (WithDim d M) :=
  NormedAddCommGroup.induced (WithDim d M) M (toValueAddEquiv d M)
    (toValueAddEquiv d M).injective

/-- The numerical-value coordinates are linear over dimensionless real scalars. -/
def toValueLinearEquiv (d : Dimension B) (M : Type) [AddCommMonoid M] [Module ℝ M] :
    WithDim d M ≃ₗ[ℝ] M where
  toFun := WithDim.val
  invFun x := ⟨x⟩
  left_inv x := by cases x; rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The induced norm is compatible with the existing real scalar multiplication. -/
instance instNormedSpace (d : Dimension B) (M : Type) [NormedAddCommGroup M]
    [NormedSpace ℝ M] : NormedSpace ℝ (WithDim d M) where
  norm_smul_le r x := norm_smul_le r x.val

@[simp]
lemma norm_eq {d : Dimension B} {M : Type} [NormedAddCommGroup M] (x : WithDim d M) :
    ‖x‖ = ‖x.val‖ := rfl

/-- Numerical-value coordinates form a linear isometry for a fixed unit representation. -/
def toValueLinearIsometryEquiv (d : Dimension B) (M : Type) [NormedAddCommGroup M]
    [NormedSpace ℝ M] : WithDim d M ≃ₗᵢ[ℝ] M :=
  { toValueLinearEquiv d M with norm_map' := fun _ => rfl }

@[simp]
lemma toValueLinearIsometryEquiv_apply (d : Dimension B) (M : Type)
    [NormedAddCommGroup M] [NormedSpace ℝ M] (x : WithDim d M) :
    toValueLinearIsometryEquiv d M x = x.val := rfl

@[simp]
lemma toValueLinearIsometryEquiv_symm_apply (d : Dimension B) (M : Type)
    [NormedAddCommGroup M] [NormedSpace ℝ M] (x : M) :
    (toValueLinearIsometryEquiv d M).symm x = (⟨x⟩ : WithDim d M) := rfl

/-!
## A.2. Transport of existing functions and derivatives
-/

/-- Express a numerical function in explicitly chosen input and output dimensions.
This definition by itself makes no claim of dimensional correctness. -/
def transport {M N : Type} (d e : Dimension B) (f : M → N) :
    WithDim d M → WithDim e N := fun x => ⟨f x.val⟩

@[simp]
lemma transport_val {M N : Type} (d e : Dimension B) (f : M → N) (x : WithDim d M) :
    (transport d e f x).val = f x.val := rfl

/-- Express a continuous linear map between tagged numerical coordinates. -/
def transportLinearMap {M N : Type} [NormedAddCommGroup M] [NormedSpace ℝ M]
    [NormedAddCommGroup N] [NormedSpace ℝ N] (d e : Dimension B) (f : M →L[ℝ] N) :
    WithDim d M →L[ℝ] WithDim e N :=
  (toValueLinearIsometryEquiv e N).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (f.comp (toValueLinearIsometryEquiv d M).toContinuousLinearEquiv.toContinuousLinearMap)

@[simp]
lemma transportLinearMap_val {M N : Type} [NormedAddCommGroup M] [NormedSpace ℝ M]
    [NormedAddCommGroup N] [NormedSpace ℝ N] (d e : Dimension B) (f : M →L[ℝ] N)
    (x : WithDim d M) : (transportLinearMap d e f x).val = f x.val := rfl

/-- Reuse a derivative in numerical coordinates for the corresponding tagged function. -/
lemma hasFDerivAt_transport {M N : Type} [NormedAddCommGroup M] [NormedSpace ℝ M]
    [NormedAddCommGroup N] [NormedSpace ℝ N] (d e : Dimension B) {f : M → N}
    {f' : M →L[ℝ] N} {x : WithDim d M} (h : HasFDerivAt f f' x.val) :
    HasFDerivAt (transport d e f) (transportLinearMap d e f') x := by
  exact (toValueLinearIsometryEquiv e N).symm.toContinuousLinearEquiv.hasFDerivAt.comp x
    (h.comp x (toValueLinearIsometryEquiv d M).toContinuousLinearEquiv.hasFDerivAt)

end WithDim
