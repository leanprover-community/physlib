/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.Classical.Nuclear

/-!
# Complete positivity of classical channels

## i. Overview

A channel acting on one part of a composite system should keep every nonnegative composite
observable nonnegative, whatever the other part is. This is complete positivity, and it depends
on which composite is used. For a channel into or out of a classical system it holds for every
choice of composites: a classical system composes uniquely, so there is only one composite to
check, and positive maps preserve the minimal and the maximal cone.

Precisely, let `A` be any Archimedean ancilla. Then `φ ⊗ id` maps every composite observable in
the maximal cone into every Archimedean cone that contains the minimal cone, whenever the input or
the output of `φ` is classical. In particular it maps any composite of the input with `A` into any
Archimedean composite of the output with `A`. For a classical input `φ` must be a channel;
for a classical output any positive map works.

## ii. Key results

- `CompositeCone.map_mem_of_isNuclear_left` : a channel out of a nuclear system is completely
  positive.
- `CompositeCone.map_mem_of_isNuclear_right` : a positive map into a nuclear system is completely
  positive.
- `CompositeCone.map_mem_of_isNuclear_left'`, `CompositeCone.map_mem_of_isNuclear_right'` : the
  same, stated for composites.
- `CompositeCone.map_mem_of_isClassical_left`, `CompositeCone.map_mem_of_isClassical_right` : the
  same for classical systems.

## iii. Table of contents

- A. Tensoring with the identity
- B. Nuclear inputs and outputs
- C. Classical inputs and outputs

-/

@[expose] public section

namespace ProbabilisticTheory

open TensorProduct

variable {E F : Type*} [OrderUnitSpace E] [OrderUnitSpace F]
  {A : Type} [ArchimedeanOrderUnitSpace A]

namespace CompositeCone

/-! ## A. Tensoring with the identity -/

/-- Applying a channel to the first part of a composite leaves the unit `1 ⊗ 1` in place. -/
lemma map_one_tmul_one (φ : Channel E F) :
    TensorProduct.map φ.toLinearMap (LinearMap.id (R := ℝ) (M := A)) ((1 : E) ⊗ₜ[ℝ] (1 : A)) =
      (1 : F) ⊗ₜ[ℝ] (1 : A) := by
  rw [map_tmul, LinearMap.id_apply]
  exact congrArg (· ⊗ₜ[ℝ] (1 : A)) φ.map_one'

/-- Applying a channel to the first part maps the Archimedean closure of the minimal cone into
itself. -/
lemma map_mem_minTensorClosure (φ : Channel E F) {z : E ⊗[ℝ] A}
    (hz : z ∈ minTensorClosure E A) :
    TensorProduct.map φ.toLinearMap LinearMap.id z ∈ minTensorClosure F A := by
  intro ε hε
  have h : TensorProduct.map φ.toLinearMap LinearMap.id (z + ε • ((1 : E) ⊗ₜ[ℝ] (1 : A))) ∈
      minTensorCone F A :=
    map_mem_minTensorCone φ.toPositiveLinearMap (PositiveLinearMap.id ℝ A) (hz ε hε)
  rwa [map_add, map_smul, map_one_tmul_one] at h

/-! ## B. Nuclear inputs and outputs -/

/-- **A channel out of a nuclear system is completely positive.** Applied to the first part of a
composite observable in the maximal cone with an Archimedean ancilla, it lands in every Archimedean
cone of composite observables that contains the minimal cone. -/
lemma map_mem_of_isNuclear_left (hE : IsNuclear E) (φ : Channel E F) {z : E ⊗[ℝ] A}
    (hz : z ∈ maxTensorCone E A) {C : PointedCone ℝ (F ⊗[ℝ] A)} (hC : IsArchimedeanTensorCone C)
    (hmin : minTensorCone F A ≤ C) : TensorProduct.map φ.toLinearMap LinearMap.id z ∈ C :=
  hC.closure_subset hmin (map_mem_minTensorClosure φ (hE A hz))

/-- **A positive map into a nuclear system is completely positive.** Applied to the first part of
a composite observable in the maximal cone with an Archimedean ancilla, it lands in every
Archimedean cone of composite observables that contains the minimal cone. -/
lemma map_mem_of_isNuclear_right (hF : IsNuclear F) (φ : E →ₚ[ℝ] F) {z : E ⊗[ℝ] A}
    (hz : z ∈ maxTensorCone E A) {C : PointedCone ℝ (F ⊗[ℝ] A)} (hC : IsArchimedeanTensorCone C)
    (hmin : minTensorCone F A ≤ C) : TensorProduct.map φ.toLinearMap LinearMap.id z ∈ C := by
  have h : TensorProduct.map φ.toLinearMap LinearMap.id z ∈ maxTensorCone F A :=
    map_mem_maxTensorCone φ (PositiveLinearMap.id ℝ A) hz
  exact hC.closure_subset hmin (hF A h)

/-- A channel out of a nuclear system maps every composite into every Archimedean composite. -/
lemma map_mem_of_isNuclear_left' (hE : IsNuclear E) (φ : Channel E F) (C₁ : CompositeCone E A)
    {C₂ : CompositeCone F A} (hC₂ : C₂.IsArchimedean) {z : E ⊗[ℝ] A} (hz : z ∈ C₁) :
    TensorProduct.map φ.toLinearMap LinearMap.id z ∈ C₂ :=
  map_mem_of_isNuclear_left hE φ (C₁.le_max hz) hC₂ C₂.min_le

/-- A positive map into a nuclear system maps every composite into every Archimedean composite. -/
lemma map_mem_of_isNuclear_right' (hF : IsNuclear F) (φ : E →ₚ[ℝ] F) (C₁ : CompositeCone E A)
    {C₂ : CompositeCone F A} (hC₂ : C₂.IsArchimedean) {z : E ⊗[ℝ] A} (hz : z ∈ C₁) :
    TensorProduct.map φ.toLinearMap LinearMap.id z ∈ C₂ :=
  map_mem_of_isNuclear_right hF φ (C₁.le_max hz) hC₂ C₂.min_le

/-! ## C. Classical inputs and outputs -/

/-- **A channel out of a classical system is completely positive.** -/
lemma map_mem_of_isClassical_left {E : Type*} [ArchimedeanOrderUnitSpace E] (hE : IsClassical E)
    (φ : Channel E F) (C₁ : CompositeCone E A) {C₂ : CompositeCone F A} (hC₂ : C₂.IsArchimedean)
    {z : E ⊗[ℝ] A} (hz : z ∈ C₁) : TensorProduct.map φ.toLinearMap LinearMap.id z ∈ C₂ :=
  map_mem_of_isNuclear_left' hE.isNuclear φ C₁ hC₂ hz

/-- **A positive map into a classical system is completely positive.** -/
lemma map_mem_of_isClassical_right {F : Type*} [ArchimedeanOrderUnitSpace F] (hF : IsClassical F)
    (φ : E →ₚ[ℝ] F) (C₁ : CompositeCone E A) {C₂ : CompositeCone F A} (hC₂ : C₂.IsArchimedean)
    {z : E ⊗[ℝ] A} (hz : z ∈ C₁) : TensorProduct.map φ.toLinearMap LinearMap.id z ∈ C₂ :=
  map_mem_of_isNuclear_right' hF.isNuclear φ C₁ hC₂ hz

end CompositeCone

end ProbabilisticTheory
