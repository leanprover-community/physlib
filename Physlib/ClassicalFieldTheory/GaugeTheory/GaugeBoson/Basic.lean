/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.DerivAlgebra
public import Mathlib.LinearAlgebra.Dual.Lemmas
/-!
# The gauge-boson field of a gauge theory

## i. Overview

The gauge bosons of a gauge theory with Lie algebra `𝔤` are jointly one bosonic field
valued in `Lorentz.CoVector ⊗[ℝ] 𝔤`: a spacetime covector with values in the gauge
algebra. Its components are the fields `A_μ^a`, but **no basis of the gauge algebra is
chosen**: the adjoint index is carried by an abstract covector `φ : Module.Dual ℝ 𝔤`
throughout.

This file is the target space alone — its linear structure, the Lorentz action, the
global gauge action, and the jet component space spanned by the component functions
`∂_s A_μ^φ`. The jet algebra built on it, and the actions and gradings it carries, are in
`Physlib.ClassicalFieldTheory.GaugeTheory.GaugeBoson.GaugeJetAlgebra`. For the Standard
Model, `𝔤` is `StandardModel.GaugeAlgebra`.

## ii. Key results

- `GaugeBoson` : the target space of the gauge-boson field.
- `GaugeBoson.repLorentzGroup` : the Lorentz action on the target space.
- `GaugeBoson.repValue` : the global gauge action on the target space, from a
  representation of the value group.
- `GaugeBoson.JetComponentSpace` : the span of the component functions `∂_s A_μ^φ`.
- `GaugeBoson.componentDual` : the covector picking out a spacetime and an adjoint index.

## iii. Table of contents

- A. The target space of the gauge-boson field
  - A.1. Linear structure
  - A.2. The Lorentz action on the target space
  - A.3. The global gauge action on the target space
- B. The jet component space
  - B.1. The component covectors

-/

@[expose] public section

set_option linter.unusedSectionVars false

variable {𝔤 : Type} [LieRing 𝔤] [LieAlgebra ℝ 𝔤] [Module.Finite ℝ 𝔤]

open TensorProduct

/-!

## A. The target space of the gauge-boson field

-/

variable (𝔤) in
/-- The target vector space of the gauge-boson field: a spacetime covector
  with values in the gauge algebra. Its components are the fields `A_μ^a`; here the
  adjoint index is kept abstract, as the gauge-algebra factor. -/
@[ext]
structure GaugeBoson where
  /-- The underlying covector-valued gauge algebra element. -/
  val : Lorentz.CoVector ⊗[ℝ] 𝔤

namespace GaugeBoson

/-!

### A.1. Linear structure

-/

variable (𝔤) in
/-- Identifies a gauge boson with its underlying tensor-product value. -/
def valEquiv : (GaugeBoson 𝔤) ≃ Lorentz.CoVector ⊗[ℝ] 𝔤 where
  toFun := val
  invFun := fun m => ⟨m⟩

noncomputable instance : AddCommGroup (GaugeBoson 𝔤) := Equiv.addCommGroup (valEquiv 𝔤)

noncomputable instance : Module ℝ (GaugeBoson 𝔤) := Equiv.module ℝ (valEquiv 𝔤)

variable (𝔤) in
/-- The linear identification with the underlying tensor product. -/
def valLinEquiv : (GaugeBoson 𝔤) ≃ₗ[ℝ] Lorentz.CoVector ⊗[ℝ] 𝔤 where
  toFun := val
  invFun := fun m => ⟨m⟩
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

@[simp]
lemma valLinEquiv_apply (v : (GaugeBoson 𝔤)) : (valLinEquiv 𝔤) v = v.val := rfl

lemma valLinEquiv_symm_apply (m : Lorentz.CoVector ⊗[ℝ] 𝔤) :
    (valLinEquiv 𝔤).symm m = ⟨m⟩ := rfl

@[simp]
lemma val_add (v₁ v₂ : (GaugeBoson 𝔤)) : (v₁ + v₂).val = v₁.val + v₂.val := rfl

@[simp]
lemma val_smul (r : ℝ) (v : (GaugeBoson 𝔤)) : (r • v).val = r • v.val := rfl

instance : Module.Finite ℝ (GaugeBoson 𝔤) :=
  Module.Finite.equiv (valLinEquiv 𝔤).symm

/-!

### A.2. The Lorentz action on the target space

-/

open Matrix MatrixGroups

variable (𝔤) in
/-- The Lorentz action on the gauge-boson target space: the covector action on the
  spacetime index, and the trivial action on the gauge-algebra factor. -/
noncomputable def repLorentzGroup : Representation ℝ SL(2,ℂ) (GaugeBoson 𝔤) where
  toFun Λ := (valLinEquiv 𝔤).symm.toLinearMap ∘ₗ
    TensorProduct.map (Lorentz.CoVector.sl2Rep Λ) LinearMap.id ∘ₗ
    (valLinEquiv 𝔤).toLinearMap
  map_one' := by
    refine LinearMap.ext fun v => ?_
    simp [Module.End.one_eq_id]
  map_mul' Λ₁ Λ₂ := by
    refine LinearMap.ext fun v => ?_
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      Module.End.mul_apply, LinearEquiv.apply_symm_apply, map_mul]
    congr 1
    rw [← LinearMap.comp_apply, ← TensorProduct.map_comp, LinearMap.id_comp]
    rfl

/-!

### A.3. The global gauge action on the target space

-/

/-- The global gauge action on the gauge-boson target space: the adjoint action on the
  gauge-algebra factor, and the trivial action on the spacetime index. -/
noncomputable def repValue {G₀ : Type} [Monoid G₀] (ρ : Representation ℝ G₀ 𝔤) :
    Representation ℝ G₀ (GaugeBoson 𝔤) where
  toFun g := (valLinEquiv 𝔤).symm.toLinearMap ∘ₗ
    TensorProduct.map LinearMap.id (ρ g) ∘ₗ
    (valLinEquiv 𝔤).toLinearMap
  map_one' := by
    refine LinearMap.ext fun v => ?_
    simp [Module.End.one_eq_id]
  map_mul' g₁ g₂ := by
    refine LinearMap.ext fun v => ?_
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      Module.End.mul_apply, LinearEquiv.apply_symm_apply, map_mul]
    congr 1
    rw [← LinearMap.comp_apply, ← TensorProduct.map_comp, LinearMap.id_comp]
    rfl

/-!

## B. The jet component space

-/

variable (𝔤) in
/-- The jet component space of the gauge-boson field: the span of the component functions
  `∂_s A_μ^φ`. The `DerivAlgebraReal` factor carries the derivative label `s`, and the
  dual factor the spacetime and adjoint indices — the latter as an abstract covector on
  the gauge algebra, with no basis chosen. Unlike a matter field, the gauge boson is real,
  so there is no conjugate half. -/
abbrev JetComponentSpace : Type :=
  DerivAlgebraReal ⊗[ℝ] Module.Dual ℝ (GaugeBoson 𝔤)

/-!

### B.1. The component covectors

-/

variable (𝔤) in
/-- The covector on the gauge-boson target space pairing the spacetime index against a
  covector `ω` and the adjoint index against `φ`. -/
noncomputable def componentDual :
    Module.Dual ℝ Lorentz.CoVector →ₗ[ℝ]
      Module.Dual ℝ 𝔤 →ₗ[ℝ] Module.Dual ℝ (GaugeBoson 𝔤) where
  toFun ω := (Module.Dual.transpose (M := (GaugeBoson 𝔤)) (valLinEquiv 𝔤).toLinearMap).comp
    ((TensorProduct.dualDistrib ℝ Lorentz.CoVector 𝔤).comp
      (TensorProduct.mk ℝ (Module.Dual ℝ Lorentz.CoVector) (Module.Dual ℝ 𝔤) ω))
  map_add' ω₁ ω₂ := by
    refine LinearMap.ext fun φ => ?_
    simp
  map_smul' r ω := by
    refine LinearMap.ext fun φ => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, TensorProduct.mk_apply,
      RingHom.id_apply, LinearMap.smul_apply]
    rw [← TensorProduct.smul_tmul', map_smul, map_smul]

@[simp]
lemma componentDual_apply_val_tmul (ω : Module.Dual ℝ Lorentz.CoVector)
    (φ : Module.Dual ℝ 𝔤) (v : Lorentz.CoVector) (a : 𝔤) :
    (componentDual 𝔤) ω φ ⟨v ⊗ₜ[ℝ] a⟩ = ω v * φ a := by
  simp [componentDual, Module.Dual.transpose_apply]

end GaugeBoson
