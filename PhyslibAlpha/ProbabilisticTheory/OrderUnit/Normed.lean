/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.Channel.Basic
public import Physlib.ProbabilisticTheory.OrderUnit.Archimedean
public import Mathlib.Analysis.Normed.Operator.LinearIsometry

/-!
# The canonical normed copy of an order-unit space

## i. Overview

An Archimedean order-unit space already has a canonical order-unit norm, but the underlying type
may carry a different norm for another purpose. `WithOrderUnitNorm E` is a type synonym that
carries the canonical norm without changing the structures on `E` itself.

## ii. Key results

- `WithOrderUnitNorm E` : the canonical normed copy of `E`.
- `WithOrderUnitNorm.linearEquiv` : the identity linear equivalence with `E`.
- `UnitalPositiveLinearMap.orderUnitNorm_map_le` : channels are contractive.

## iii. Table of contents

- A. The normed copy
- B. The real scalar case
- C. Contractivity of channels
-/

@[expose] public section

namespace ProbabilisticTheory

open ArchimedeanOrderUnitSpace

/-! ## A. The normed copy -/

/-- A type synonym of `E` carrying its canonical order-unit norm. -/
def WithOrderUnitNorm (E : Type*) := E

namespace ArchimedeanOrderUnitSpace

variable {E : Type*} [ArchimedeanOrderUnitSpace E]

/-- Membership in the symmetric order-unit interval is equivalent to the norm bound. -/
lemma mem_orderUnitBounds_iff {A : E} {r : ℝ} :
    r ∈ orderUnitBounds A ↔ orderUnitNorm A ≤ r := by
  rw [orderUnitNorm_le_iff]
  rfl

/-- For the classical order unit on `ℝ`, the order-unit norm is absolute value. -/
lemma orderUnitNorm_real (x : ℝ) : orderUnitNorm x = |x| := by
  apply le_antisymm
  · exact orderUnitNorm_le ⟨abs_nonneg x, by simpa [smul_eq_mul] using neg_abs_le x,
      by simpa [smul_eq_mul] using le_abs_self x⟩
  · apply abs_le.mpr
    exact ⟨by simpa [smul_eq_mul] using neg_orderUnitNorm_smul_one_le x,
      by simpa [smul_eq_mul] using le_orderUnitNorm_smul_one x⟩

end ArchimedeanOrderUnitSpace

namespace WithOrderUnitNorm

variable {E : Type*} [ArchimedeanOrderUnitSpace E]

instance : AddCommGroup (WithOrderUnitNorm E) := inferInstanceAs (AddCommGroup E)
instance : Module ℝ (WithOrderUnitNorm E) := inferInstanceAs (Module ℝ E)
instance : PartialOrder (WithOrderUnitNorm E) := inferInstanceAs (PartialOrder E)
instance : IsOrderedAddMonoid (WithOrderUnitNorm E) := inferInstanceAs (IsOrderedAddMonoid E)
instance : PosSMulMono ℝ (WithOrderUnitNorm E) := inferInstanceAs (PosSMulMono ℝ E)
instance : One (WithOrderUnitNorm E) := inferInstanceAs (One E)
instance : OrderUnitSpace (WithOrderUnitNorm E) := inferInstanceAs (OrderUnitSpace E)
instance : ArchimedeanOrderUnitSpace (WithOrderUnitNorm E) :=
  inferInstanceAs (ArchimedeanOrderUnitSpace E)

/-- The canonical normed additive group on the order-unit-norm copy. -/
noncomputable instance : NormedAddCommGroup (WithOrderUnitNorm E) :=
  ArchimedeanOrderUnitSpace.orderUnitNormedAddCommGroup

/-- The canonical real normed-space structure on the order-unit-norm copy. -/
noncomputable instance : NormedSpace ℝ (WithOrderUnitNorm E) :=
  ArchimedeanOrderUnitSpace.orderUnitNormedSpace

/-- The identity linear equivalence from `E` to its order-unit-norm copy. -/
def linearEquiv : E ≃ₗ[ℝ] WithOrderUnitNorm E := LinearEquiv.refl ℝ E

@[simp]
lemma linearEquiv_apply (x : E) : linearEquiv x = x := rfl

@[simp]
lemma norm_eq_orderUnitNorm (x : WithOrderUnitNorm E) :
    ‖x‖ = orderUnitNorm (show E from x) := rfl

/-! ## B. The real scalar case -/

/-- The scalar order-unit-norm copy is linearly isometric to ordinary `ℝ`. -/
noncomputable def realLinearIsometryEquiv : WithOrderUnitNorm ℝ ≃ₗᵢ[ℝ] ℝ where
  __ := (linearEquiv (E := ℝ)).symm
  norm_map' x := by
    change |(show ℝ from x)| = orderUnitNorm (show ℝ from x)
    exact (ArchimedeanOrderUnitSpace.orderUnitNorm_real _).symm

@[simp]
lemma realLinearIsometryEquiv_apply (x : WithOrderUnitNorm ℝ) :
    realLinearIsometryEquiv x = (show ℝ from x) := rfl

/-- The scalar order-unit-norm copy is complete via its canonical isometry to `ℝ`. -/
noncomputable instance : CompleteSpace (WithOrderUnitNorm ℝ) :=
  (completeSpace_congr (e := realLinearIsometryEquiv.toLinearEquiv.toEquiv)
    realLinearIsometryEquiv.isometry.isUniformEmbedding).mpr inferInstance

end WithOrderUnitNorm

/-! ## C. Contractivity of channels -/

namespace UnitalPositiveLinearMap

variable {E F : Type*} [ArchimedeanOrderUnitSpace E] [ArchimedeanOrderUnitSpace F]

/-- A unital positive map is contractive for the order-unit norms. -/
lemma orderUnitNorm_map_le (φ : Channel E F) (x : E) :
    orderUnitNorm (φ x) ≤ orderUnitNorm x := by
  apply orderUnitNorm_le_iff.mpr
  refine ⟨orderUnitNorm_nonneg x, ?_, ?_⟩
  · calc
      -(orderUnitNorm x • (1 : F)) = φ (-(orderUnitNorm x • (1 : E))) := by
        rw [map_neg, map_smul, map_one]
      _ ≤ φ x := φ.monotone' (neg_orderUnitNorm_smul_one_le x)
  · calc
      φ x ≤ φ (orderUnitNorm x • (1 : E)) :=
        φ.monotone' (le_orderUnitNorm_smul_one x)
      _ = orderUnitNorm x • (1 : F) := by rw [map_smul, map_one]

end UnitalPositiveLinearMap

end ProbabilisticTheory
