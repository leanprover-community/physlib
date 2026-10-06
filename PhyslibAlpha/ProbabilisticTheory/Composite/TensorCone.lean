/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.State.Separation
public import Physlib.ProbabilisticTheory.OrderUnit.Cone
public import PhyslibAlpha.Mathematics.Convex.DominatedCone
public import Mathlib.Geometry.Convex.Cone.TensorProduct
public import Mathlib.LinearAlgebra.TensorProduct.Associator

/-!
# Composite systems

Composite systems: the minimal and maximal tensor cones, composites, and nuclear systems.

## i. Overview

Two systems with observables `E` and `F` are combined into a composite system whose observables
are the tensor products `E ⊗ F`. Which composite observables are nonnegative is not fixed by the
parts; there are two extreme choices.

The minimal cone contains only the sums of products `x ⊗ y` of nonnegative observables: nonnegative
local observations. The maximal cone contains every composite observable that no pair of local
preparations `φ ⊗ ψ` can assign a negative value. A composite of `E` and `F` is any choice of
nonnegative composite observables in between. Tensor products of positive maps preserve both
extreme cones.

A system is nuclear when, for every other system, the maximal cone lies in the closure of the
minimal cone: its composites are unique.

## ii. Key results

- `Composite E F` : the observables of the composite system.
- `PositiveLinearMap.tensor` : the product functional `φ ⊗ ψ`.
- `minTensorCone E F`, `maxTensorCone E F` : the minimal and the maximal cone.
- `mem_maxTensorCone` : the maximal cone consists of the composite observables that every product
  functional keeps nonnegative.
- `minTensorCone_map_le`, `maxTensorCone_map_le` : tensor products of positive maps preserve the
  minimal and the maximal cone.
- `CompositeCone E F` : a composite of `E` and `F`.
- `isDominatedCone_minTensorCone` : every composite observable plus a large multiple of `1 ⊗ 1` lies
  in the minimal cone.
- `minTensorClosure E F` : the Archimedean closure of the minimal cone.
- `IsNuclear E` : composition with every Archimedean system is unique, up to closure.
- `mem_maxTensorCone_iff_rslice` : for Archimedean `E`, the maximal cone consists of the composite
  observables that stay nonnegative when a positive functional is applied to the second factor.

## iii. Table of contents

- A. Slices and product functionals
- B. The minimal and the maximal cone
- C. Tensor products of positive maps
- D. Composites
- E. The closure of the minimal cone and nuclear systems

## iv. References

* None.

-/

@[expose] public section

namespace ProbabilisticTheory

open TensorProduct
open scoped NNReal

variable {E F : Type*} [OrderUnitSpace E] [OrderUnitSpace F]

variable (E F) in
/-- The observables of the composite of two systems: the tensor products `E ⊗ F`. -/
abbrev Composite : Type _ := E ⊗[ℝ] F

/-- The product `x ⊗ y` of observables of the two parts, as a composite observable. -/
abbrev Composite.tmul (x : E) (y : F) : Composite E F := x ⊗ₜ[ℝ] y

/-! ## A. Slices and product functionals -/

end ProbabilisticTheory

namespace PositiveLinearMap
open ProbabilisticTheory
open TensorProduct
open scoped NNReal
variable {E F : Type*} [OrderUnitSpace E] [OrderUnitSpace F]

/-- Apply a positive functional to the second factor. -/
noncomputable def rslice (ψ : F →ₚ[ℝ] ℝ) : E ⊗[ℝ] F →ₗ[ℝ] E :=
  (TensorProduct.rid ℝ E).toLinearMap ∘ₗ TensorProduct.map LinearMap.id ψ.toLinearMap

/-- Apply a positive functional to the first factor. -/
noncomputable def lslice (φ : E →ₚ[ℝ] ℝ) : E ⊗[ℝ] F →ₗ[ℝ] F :=
  (TensorProduct.lid ℝ F).toLinearMap ∘ₗ TensorProduct.map φ.toLinearMap LinearMap.id

@[simp]
lemma rslice_tmul (ψ : F →ₚ[ℝ] ℝ) (x : E) (y : F) : rslice ψ (x ⊗ₜ[ℝ] y) = ψ y • x := by
  simp [rslice]

@[simp]
lemma lslice_tmul (φ : E →ₚ[ℝ] ℝ) (x : E) (y : F) : lslice φ (x ⊗ₜ[ℝ] y) = φ x • y := by
  simp [lslice]

/-- The product functional `φ ⊗ ψ`. -/
noncomputable def tensor (φ : E →ₚ[ℝ] ℝ) (ψ : F →ₚ[ℝ] ℝ) : E ⊗[ℝ] F →ₗ[ℝ] ℝ :=
  φ.toLinearMap ∘ₗ rslice ψ

@[simp]
lemma tensor_tmul (φ : E →ₚ[ℝ] ℝ) (ψ : F →ₚ[ℝ] ℝ) (x : E) (y : F) :
    tensor φ ψ (x ⊗ₜ[ℝ] y) = φ x * ψ y := by
  simp [tensor, mul_comm]

lemma tensor_apply (φ : E →ₚ[ℝ] ℝ) (ψ : F →ₚ[ℝ] ℝ) (z : E ⊗[ℝ] F) :
    tensor φ ψ z = φ (rslice ψ z) :=
  rfl

lemma tensor_apply_eq_lslice (φ : E →ₚ[ℝ] ℝ) (ψ : F →ₚ[ℝ] ℝ) (z : E ⊗[ℝ] F) :
    tensor φ ψ z = ψ (lslice φ z) := by
  change tensor φ ψ z = (ψ.toLinearMap ∘ₗ lslice φ) z
  congr 1
  exact TensorProduct.ext' fun x y => by simp

end PositiveLinearMap

namespace ProbabilisticTheory

open TensorProduct
open scoped NNReal
variable {E F : Type*} [OrderUnitSpace E] [OrderUnitSpace F]

/-! ## B. The minimal and the maximal cone -/

open PositiveLinearMap

variable (E F) in
/-- The minimal tensor cone: sums of products of nonnegative observables. -/
noncomputable def minTensorCone : PointedCone ℝ (E ⊗[ℝ] F) :=
  .minTensorProduct (PosCone E) (PosCone F)

variable (E F) in
/-- The maximal tensor cone: composite observables to which no product of positive functionals
assigns a negative value. -/
noncomputable def maxTensorCone : PointedCone ℝ (E ⊗[ℝ] F) :=
  .maxTensorProduct (PosCone E) (PosCone F)

lemma tmul_mem_minTensorCone {x : E} {y : F} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x ⊗ₜ[ℝ] y ∈ minTensorCone E F :=
  PointedCone.tmul_mem_minTensorProduct ((PointedCone.mem_positive _ _).2 hx)
    ((PointedCone.mem_positive _ _).2 hy)

lemma smul_mem_minTensorCone {c : ℝ} (hc : 0 ≤ c) {w : E ⊗[ℝ] F} (hw : w ∈ minTensorCone E F) :
    c • w ∈ minTensorCone E F :=
  (minTensorCone E F).smul_mem hc hw

/-- An induction principle for the minimal cone: a property of composite observables that holds
for products of nonnegative observables and is stable under sums and nonnegative multiples holds
on the whole minimal cone. -/
lemma minTensorCone_induction {p : E ⊗[ℝ] F → Prop} {z : E ⊗[ℝ] F} (hz : z ∈ minTensorCone E F)
    (tmul : ∀ x y, 0 ≤ x → 0 ≤ y → p (x ⊗ₜ[ℝ] y)) (zero : p 0)
    (add : ∀ z w, p z → p w → p (z + w)) (smul : ∀ c : ℝ, 0 ≤ c → ∀ z, p z → p (c • z)) :
    p z := by
  induction hz using Submodule.span_induction with
  | mem _ h =>
    obtain ⟨x, hx, y, hy, rfl⟩ := h
    exact tmul x y ((PointedCone.mem_positive _ _).1 hx) ((PointedCone.mem_positive _ _).1 hy)
  | zero => exact zero
  | add _ _ _ _ h₁ h₂ => exact add _ _ h₁ h₂
  | smul c _ _ h => exact smul c c.2 _ h

/-- The product functional of positive functionals is the pairing with their dual tensor. -/
lemma tensor_eq_dualDistrib (φ : E →ₚ[ℝ] ℝ) (ψ : F →ₚ[ℝ] ℝ) (z : E ⊗[ℝ] F) :
    tensor φ ψ z = dualDistrib ℝ E F (φ.toLinearMap ⊗ₜ[ℝ] ψ.toLinearMap) z := by
  induction z using TensorProduct.inductionOn with
  | tmul x y => simp
  | add z w hz hw => rw [map_add, map_add, hz, hw]

/-- A composite observable is in the maximal cone exactly when every product of positive
functionals assigns it a nonnegative value. -/
lemma mem_maxTensorCone {z : E ⊗[ℝ] F} :
    z ∈ maxTensorCone E F ↔ ∀ (φ : E →ₚ[ℝ] ℝ) (ψ : F →ₚ[ℝ] ℝ), 0 ≤ tensor φ ψ z := by
  simp only [maxTensorCone, PointedCone.mem_maxTensorProduct, tensor_eq_dualDistrib]
  refine ⟨fun h φ ψ => h _ (fun x hx => φ.map_nonneg ((PointedCone.mem_positive _ _).1 hx)) _
    (fun y hy => ψ.map_nonneg ((PointedCone.mem_positive _ _).1 hy)), fun h f hf g hg => ?_⟩
  exact h (.mk₀ f fun x hx => hf ((PointedCone.mem_positive _ _).2 hx))
    (.mk₀ g fun y hy => hg ((PointedCone.mem_positive _ _).2 hy))

/-- Every observable in the minimal cone is in the maximal cone. -/
lemma minTensorCone_le_maxTensorCone : minTensorCone E F ≤ maxTensorCone E F :=
  PointedCone.minTensorProduct_le_maxTensorProduct _ _

/-! ## C. Tensor products of positive maps -/

section Map

variable {E' F' : Type*} [OrderUnitSpace E'] [OrderUnitSpace F']

lemma posCone_map_le (φ : E →ₚ[ℝ] E') : (PosCone E).map φ.toLinearMap ≤ PosCone E' := by
  rintro _ ⟨x, hx, rfl⟩
  exact (PointedCone.mem_positive _ _).2 (φ.map_nonneg ((PointedCone.mem_positive _ _).1 hx))

/-- Tensor products of positive maps preserve the minimal cone. -/
lemma minTensorCone_map_le (φ : E →ₚ[ℝ] E') (ψ : F →ₚ[ℝ] F') :
    (minTensorCone E F).map (TensorProduct.map φ.toLinearMap ψ.toLinearMap) ≤
      minTensorCone E' F' :=
  (PointedCone.minTensorProduct_map_le _ _ _ _).trans
    (PointedCone.minTensorProduct_mono (posCone_map_le φ) (posCone_map_le ψ))

/-- Tensor products of positive maps preserve the maximal cone. -/
lemma maxTensorCone_map_le (φ : E →ₚ[ℝ] E') (ψ : F →ₚ[ℝ] F') :
    (maxTensorCone E F).map (TensorProduct.map φ.toLinearMap ψ.toLinearMap) ≤
      maxTensorCone E' F' :=
  (PointedCone.maxTensorProduct_map_le _ _ _ _).trans
    (PointedCone.maxTensorProduct_mono (posCone_map_le φ) (posCone_map_le ψ))

lemma map_mem_minTensorCone (φ : E →ₚ[ℝ] E') (ψ : F →ₚ[ℝ] F') {z : E ⊗[ℝ] F}
    (hz : z ∈ minTensorCone E F) :
    TensorProduct.map φ.toLinearMap ψ.toLinearMap z ∈ minTensorCone E' F' :=
  minTensorCone_map_le φ ψ ⟨z, hz, rfl⟩

lemma map_mem_maxTensorCone (φ : E →ₚ[ℝ] E') (ψ : F →ₚ[ℝ] F') {z : E ⊗[ℝ] F}
    (hz : z ∈ maxTensorCone E F) :
    TensorProduct.map φ.toLinearMap ψ.toLinearMap z ∈ maxTensorCone E' F' :=
  maxTensorCone_map_le φ ψ ⟨z, hz, rfl⟩

end Map

/-! ## D. Composites -/

/-- A cone of composite observables is Archimedean when a composite observable that becomes
nonnegative after adding any positive multiple of the unit `1 ⊗ 1` is already nonnegative. -/
def IsArchimedeanTensorCone (C : PointedCone ℝ (E ⊗[ℝ] F)) : Prop :=
  ∀ z : E ⊗[ℝ] F, (∀ ε : ℝ, 0 < ε → z + ε • ((1 : E) ⊗ₜ[ℝ] (1 : F)) ∈ C) → z ∈ C

variable (E F) in
/-- A composite of two systems: a choice of nonnegative composite observables that contains every
product of nonnegative observables and that no product of positive functionals makes negative. -/
structure CompositeCone where
  /-- The nonnegative composite observables. -/
  toPointedCone : PointedCone ℝ (E ⊗[ℝ] F)
  /-- Products of nonnegative observables are nonnegative. -/
  min_le : minTensorCone E F ≤ toPointedCone
  /-- Products of positive functionals stay nonnegative. -/
  le_max : toPointedCone ≤ maxTensorCone E F

namespace CompositeCone

instance : SetLike (CompositeCone E F) (E ⊗[ℝ] F) where
  coe C := C.toPointedCone
  coe_injective C D h := by
    cases C; cases D; congr; exact SetLike.coe_injective h

lemma mem_toPointedCone {C : CompositeCone E F} {z : E ⊗[ℝ] F} :
    z ∈ C.toPointedCone ↔ z ∈ C := Iff.rfl

@[ext]
lemma ext {C D : CompositeCone E F} (h : ∀ z, z ∈ C ↔ z ∈ D) : C = D := SetLike.ext h

lemma tmul_mem (C : CompositeCone E F) {x : E} {y : F} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x ⊗ₜ[ℝ] y ∈ C :=
  C.min_le (tmul_mem_minTensorCone hx hy)

/-- Every product of positive functionals is nonnegative on a composite. -/
lemma tensor_nonneg (C : CompositeCone E F) (φ : E →ₚ[ℝ] ℝ) (ψ : F →ₚ[ℝ] ℝ) {z : E ⊗[ℝ] F}
    (hz : z ∈ C) : 0 ≤ tensor φ ψ z :=
  mem_maxTensorCone.1 (C.le_max hz) φ ψ

/-- The elements of a composite form an `ℝ≥0`-module. -/
instance instModuleNNReal (C : CompositeCone E F) : Module ℝ≥0 C.toPointedCone where
  smul c x := ⟨(c : ℝ) • (x : E ⊗[ℝ] F), C.toPointedCone.smul_mem c.2 x.2⟩
  one_smul _ := Subtype.ext (one_smul ℝ _)
  mul_smul c d _ := Subtype.ext (mul_smul (c : ℝ) (d : ℝ) _)
  smul_zero _ := Subtype.ext (smul_zero _)
  smul_add c _ _ := Subtype.ext (smul_add (c : ℝ) _ _)
  add_smul c d _ := Subtype.ext (by push_cast; exact add_smul (c : ℝ) (d : ℝ) _)
  zero_smul _ := Subtype.ext (by push_cast; exact zero_smul ℝ _)

variable (E F) in
/-- The minimal composite. -/
noncomputable def minimal : CompositeCone E F :=
  ⟨minTensorCone E F, le_rfl, minTensorCone_le_maxTensorCone⟩

variable (E F) in
/-- The maximal composite. -/
noncomputable def maximal : CompositeCone E F :=
  ⟨maxTensorCone E F, minTensorCone_le_maxTensorCone, le_rfl⟩

/-- A composite is Archimedean when a composite observable that becomes nonnegative after adding
any positive multiple of the unit `1 ⊗ 1` is already nonnegative. -/
def IsArchimedean (C : CompositeCone E F) : Prop := IsArchimedeanTensorCone C.toPointedCone

/-- For fixed `0 ≤ y₀`, tensoring on the right with `y₀` maps nonnegative observables of `E`
`ℝ≥0`-linearly into any composite. -/
def tmulRight (C : CompositeCone E F) {y₀ : F} (hy₀ : 0 ≤ y₀) :
    PosCone E →ₗ[ℝ≥0] C.toPointedCone where
  toFun x := ⟨(x : E) ⊗ₜ[ℝ] y₀, C.tmul_mem ((PointedCone.mem_positive _ _).1 x.2) hy₀⟩
  map_add' _ _ := Subtype.ext (TensorProduct.add_tmul _ _ _)
  map_smul' c x := Subtype.ext (TensorProduct.smul_tmul' (c : ℝ) (x : E) y₀).symm

@[simp]
lemma tmulRight_apply (C : CompositeCone E F) {y₀ : F} (hy₀ : 0 ≤ y₀) (x : PosCone E) :
    (C.tmulRight hy₀ x : E ⊗[ℝ] F) = (x : E) ⊗ₜ[ℝ] y₀ := rfl

/-- For fixed `0 ≤ x₀`, tensoring on the left with `x₀` maps nonnegative observables of `F`
`ℝ≥0`-linearly into any composite. -/
def tmulLeft (C : CompositeCone E F) {x₀ : E} (hx₀ : 0 ≤ x₀) :
    PosCone F →ₗ[ℝ≥0] C.toPointedCone where
  toFun y := ⟨x₀ ⊗ₜ[ℝ] (y : F), C.tmul_mem hx₀ ((PointedCone.mem_positive _ _).1 y.2)⟩
  map_add' _ _ := Subtype.ext (TensorProduct.tmul_add _ _ _)
  map_smul' c y := Subtype.ext (TensorProduct.tmul_smul (R := ℝ) (c : ℝ) x₀ (y : F))

@[simp]
lemma tmulLeft_apply (C : CompositeCone E F) {x₀ : E} (hx₀ : 0 ≤ x₀) (y : PosCone F) :
    (C.tmulLeft hx₀ y : E ⊗[ℝ] F) = x₀ ⊗ₜ[ℝ] (y : F) := rfl

end CompositeCone

/-- Every composite observable is a difference of two sums of products of nonnegative
observables. -/
lemma exists_eq_sub_minTensorCone (t : E ⊗[ℝ] F) :
    ∃ tp ∈ minTensorCone E F, ∃ tn ∈ minTensorCone E F, t = tp - tn := by
  induction t using TensorProduct.inductionOn with
  | tmul x y =>
    obtain ⟨xp, xn, hxp, hxn, rfl⟩ := OrderUnitSpace.exists_eq_sub_nonneg x
    obtain ⟨yp, yn, hyp, hyn, rfl⟩ := OrderUnitSpace.exists_eq_sub_nonneg y
    refine ⟨xp ⊗ₜ[ℝ] yp + xn ⊗ₜ[ℝ] yn,
      add_mem (tmul_mem_minTensorCone hxp hyp) (tmul_mem_minTensorCone hxn hyn),
      xp ⊗ₜ[ℝ] yn + xn ⊗ₜ[ℝ] yp,
      add_mem (tmul_mem_minTensorCone hxp hyn) (tmul_mem_minTensorCone hxn hyp), ?_⟩
    simp only [TensorProduct.sub_tmul, TensorProduct.tmul_sub]
    abel
  | add t₁ t₂ h₁ h₂ =>
    obtain ⟨ap, hap, an, han, rfl⟩ := h₁
    obtain ⟨bp, hbp, bn, hbn, rfl⟩ := h₂
    exact ⟨ap + bp, add_mem hap hbp, an + bn, add_mem han hbn, by abel⟩

/-! ## E. The closure of the minimal cone and nuclear systems -/

/-- A product plus a large enough multiple of `1 ⊗ 1` lies in the minimal cone:
`x ⊗ y + (a * b) • (1 ⊗ 1)` is half the sum of `(a • 1 ± x) ⊗ (b • 1 ± y)`. -/
lemma exists_tmul_add_smul_mem (x : E) (y : F) :
    ∃ t : ℝ, x ⊗ₜ[ℝ] y + t • ((1 : E) ⊗ₜ[ℝ] (1 : F)) ∈ minTensorCone E F := by
  obtain ⟨a, hxlo, hxhi⟩ := OrderUnitSpace.exists_two_sided_bound x
  obtain ⟨b, hylo, hyhi⟩ := OrderUnitSpace.exists_two_sided_bound y
  rw [← Nat.cast_smul_eq_nsmul ℝ] at hxlo hxhi hylo hyhi
  have h₁ := tmul_mem_minTensorCone (neg_le_iff_add_nonneg'.1 hxlo) (neg_le_iff_add_nonneg'.1 hylo)
  have h₂ := tmul_mem_minTensorCone (sub_nonneg.2 hxhi) (sub_nonneg.2 hyhi)
  refine ⟨(a : ℝ) * b, ?_⟩
  have := smul_mem_minTensorCone (by norm_num : (0 : ℝ) ≤ 1 / 2) (add_mem h₁ h₂)
  convert this using 1
  simp only [add_tmul, tmul_add, sub_tmul, tmul_sub, ← smul_tmul', tmul_smul, smul_smul,
    smul_add, smul_sub]
  module

/-- Every composite observable plus a large enough multiple of `1 ⊗ 1` lies in the minimal cone. -/
lemma exists_add_smul_mem (z : E ⊗[ℝ] F) :
    ∃ t : ℝ, z + t • ((1 : E) ⊗ₜ[ℝ] (1 : F)) ∈ minTensorCone E F := by
  induction z using TensorProduct.inductionOn with
  | tmul x y => exact exists_tmul_add_smul_mem x y
  | add z z' hz hz' =>
    obtain ⟨t, ht⟩ := hz
    obtain ⟨t', ht'⟩ := hz'
    refine ⟨t + t', ?_⟩
    have e : z + z' + (t + t') • ((1 : E) ⊗ₜ[ℝ] (1 : F)) =
        (z + t • ((1 : E) ⊗ₜ[ℝ] (1 : F))) + (z' + t' • ((1 : E) ⊗ₜ[ℝ] (1 : F))) := by
      rw [add_smul]; abel
    rw [e]; exact add_mem ht ht'

/-- The minimal cone is a convex cone dominated by `1 ⊗ 1`. -/
lemma isDominatedCone_minTensorCone :
    IsDominatedCone (minTensorCone E F : Set (E ⊗[ℝ] F)) ((1 : E) ⊗ₜ[ℝ] (1 : F)) where
  zero_mem := zero_mem _
  add_mem _ ha _ hb := add_mem ha hb
  smul_mem _ hc _ ha := smul_mem_minTensorCone hc ha
  mem := tmul_mem_minTensorCone OrderUnitSpace.one_nonneg OrderUnitSpace.one_nonneg
  dominates := exists_add_smul_mem

variable (E F) in
/-- The Archimedean closure of the minimal cone: composite observables that become sums of products
of nonnegative observables after adding any positive multiple of the unit `1 ⊗ 1`. -/
def minTensorClosure : Set (E ⊗[ℝ] F) :=
  {z | ∀ ε : ℝ, 0 < ε → z + ε • ((1 : E) ⊗ₜ[ℝ] (1 : F)) ∈ minTensorCone E F}

lemma minTensorCone_subset_closure :
    (minTensorCone E F : Set (E ⊗[ℝ] F)) ⊆ minTensorClosure E F := by
  intro z hz ε hε
  have h : (ε • (1 : E)) ⊗ₜ[ℝ] (1 : F) ∈ minTensorCone E F :=
    tmul_mem_minTensorCone (smul_nonneg hε.le OrderUnitSpace.one_nonneg) OrderUnitSpace.one_nonneg
  rw [← smul_tmul'] at h
  exact add_mem hz h

/-- The closure of the minimal cone lies in the maximal cone. -/
lemma minTensorClosure_subset_maxTensorCone :
    minTensorClosure E F ⊆ (maxTensorCone E F : Set (E ⊗[ℝ] F)) :=
  fun z hz => mem_maxTensorCone.2 fun φ ψ => le_of_forall_pos_le_add fun ε hε => by
    have hφ : 0 ≤ φ 1 := map_nonneg φ OrderUnitSpace.one_nonneg
    have hψ : 0 ≤ ψ 1 := map_nonneg ψ OrderUnitSpace.one_nonneg
    have := mem_maxTensorCone.1 (minTensorCone_le_maxTensorCone
      (hz (ε / (φ 1 * ψ 1 + 1)) (by positivity))) φ ψ
    rw [map_add, map_smul, tensor_tmul, smul_eq_mul] at this
    have h : ε / (φ 1 * ψ 1 + 1) * (φ 1 * ψ 1) ≤ ε := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]; nlinarith
    linarith

/-- An Archimedean cone containing the minimal cone contains its closure. -/
lemma IsArchimedeanTensorCone.closure_subset {C : PointedCone ℝ (E ⊗[ℝ] F)}
    (hC : IsArchimedeanTensorCone C) (hmin : minTensorCone E F ≤ C) :
    minTensorClosure E F ⊆ C := fun z hz => hC z fun ε hε => hmin (hz ε hε)

/-- An Archimedean composite contains the closure of the minimal cone. -/
lemma CompositeCone.IsArchimedean.closure_subset {C : CompositeCone E F} (hC : C.IsArchimedean) :
    minTensorClosure E F ⊆ C := IsArchimedeanTensorCone.closure_subset hC C.min_le

variable (E) in
/-- A system is nuclear when it composes uniquely with every Archimedean system: every composite
observable in the maximal cone lies in the closure of the minimal cone. -/
def IsNuclear : Prop :=
  ∀ (F : Type) [ArchimedeanOrderUnitSpace F],
    (maxTensorCone E F : Set (E ⊗[ℝ] F)) ⊆ minTensorClosure E F

section Archimedean

variable {E : Type*} [ArchimedeanOrderUnitSpace E]

/-- For Archimedean `E`, a composite observable is in the maximal cone exactly when applying any
positive functional to the second factor leaves a nonnegative observable. -/
lemma mem_maxTensorCone_iff_rslice {z : E ⊗[ℝ] F} :
    z ∈ maxTensorCone E F ↔ ∀ ψ : F →ₚ[ℝ] ℝ, 0 ≤ rslice ψ z := by
  refine ⟨fun h ψ => (UnitalPositiveLinearMap.nonneg_iff_forall_state_nonneg _).2 fun ω => ?_,
    fun h => mem_maxTensorCone.2 fun φ ψ => map_nonneg φ (h ψ)⟩
  exact mem_maxTensorCone.1 h ω.toPositiveLinearMap ψ

end Archimedean

end ProbabilisticTheory
