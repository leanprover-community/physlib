/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.SpaceAndTime.SpaceTime.SpaceTimeDerivAlgebra
public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.GlobalGaugeGroup.LieAlgebra.Basic
/-!
# The gauge-boson field of a gauge theory

The target space of the gauge bosons, a spacetime covector with values in the gauge algebra.

## i. Overview

The gauge bosons of a gauge theory with Lie algebra `G.lieSubalgebra` are jointly one bosonic field
valued in `Lorentz.CoVector ⊗[ℝ] G.lieSubalgebra`, a spacetime covector with values in the gauge
algebra. Its components are the fields `A_μ^a`, but no basis of the gauge algebra is
chosen. The adjoint index is carried by an abstract covector `φ : Module.Dual ℝ G.lieSubalgebra`
throughout.

This file is the target space alone, with its linear structure, the Lorentz action, the
global gauge action, and the field-derivative space spanned by the component functions
`∂_s A_μ^φ`. The jet algebra built on it, and the actions and gradings it carries, are in the
directory
`PhyslibAlpha/ClassicalFieldTheory/GaugeTheory/GaugeBoson/LocalGaugeFieldAlgebra`. For the Standard
Model, `G.lieSubalgebra` is `StandardModel.GaugeAlgebra`.

## ii. Key results

- `GaugeBoson` : the target space of the gauge-boson field.
- `GaugeBoson.repLorentzGroup` : the Lorentz action on the target space.
- `GaugeBoson.repValue` : the global gauge action on the target space, from a
  representation of the value group.
- `GaugeBoson.FieldDerivSpace` : the span of the component functions `∂_s A_μ^φ`.
- `GaugeBoson.componentDual` : the covector picking out a spacetime and an adjoint index.
- `GaugeBoson.dual_eq_sum_componentDual` : every covector on the target space is a sum of
  component covectors.

## iii. Table of contents

- A. The target space of the gauge-boson field
  - A.1. Linear structure
  - A.2. The Lorentz action on the target space
  - A.3. The global gauge action on the target space
- B. The field-derivative space
  - B.1. The component covectors

## iv. References

* None.

-/

@[expose] public section

set_option linter.unusedSectionVars false

variable {κ : Type} [Fintype κ] [DecidableEq κ] {G : GlobalGaugeGroup κ}

open TensorProduct

/-!

## A. The target space of the gauge-boson field

-/

variable (G) in
/-- The target vector space of the gauge-boson field, a spacetime covector
  with values in the gauge algebra. Its components are the fields `A_μ^a`, and here the
  adjoint index is kept abstract, as the gauge-algebra factor. -/
@[ext]
structure GaugeBoson where
  /-- The underlying covector-valued gauge algebra element. -/
  val : Lorentz.CoVector ⊗[ℝ] G.lieSubalgebra

namespace GaugeBoson

/-!

### A.1. Linear structure

-/

variable (G) in
/-- Identifies a gauge boson with its underlying tensor-product value. -/
def valEquiv : (GaugeBoson G) ≃ Lorentz.CoVector ⊗[ℝ] G.lieSubalgebra where
  toFun := val
  invFun := fun m => ⟨m⟩

noncomputable instance : AddCommGroup (GaugeBoson G) := Equiv.addCommGroup (valEquiv G)

noncomputable instance : Module ℝ (GaugeBoson G) :=
  AddEquiv.module ℝ { valEquiv G with map_add' _ _ := rfl }

variable (G) in
/-- The linear identification with the underlying tensor product. -/
def valLinEquiv : (GaugeBoson G) ≃ₗ[ℝ] Lorentz.CoVector ⊗[ℝ] G.lieSubalgebra where
  toFun := val
  invFun := fun m => ⟨m⟩
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

@[simp]
lemma valLinEquiv_apply (v : (GaugeBoson G)) : (valLinEquiv G) v = v.val := rfl

lemma valLinEquiv_symm_apply (m : Lorentz.CoVector ⊗[ℝ] G.lieSubalgebra) :
    (valLinEquiv G).symm m = ⟨m⟩ := rfl

@[simp]
lemma val_add (v₁ v₂ : (GaugeBoson G)) : (v₁ + v₂).val = v₁.val + v₂.val := rfl

@[simp]
lemma val_smul (r : ℝ) (v : (GaugeBoson G)) : (r • v).val = r • v.val := rfl

instance : Module.Finite ℝ (GaugeBoson G) :=
  Module.Finite.equiv (valLinEquiv G).symm

/-!

### A.2. The Lorentz action on the target space

-/

open Matrix MatrixGroups

variable (G) in
/-- The Lorentz action on the gauge-boson target space, the covector action on the
  spacetime index and the trivial action on the gauge-algebra factor. -/
noncomputable def repLorentzGroup : Representation ℝ SL(2,ℂ) (GaugeBoson G) where
  toFun Λ := (valLinEquiv G).symm.toLinearMap ∘ₗ
    TensorProduct.map (Lorentz.CoVector.sl2Rep Λ) LinearMap.id ∘ₗ
    (valLinEquiv G).toLinearMap
  map_one' := by
    refine LinearMap.ext fun v => ?_
    simp [Module.End.one_eq_id]
  map_mul' Λ₁ Λ₂ := by
    refine LinearMap.ext fun v => ?_
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      mul_apply_eq_comp, LinearEquiv.apply_symm_apply, map_mul]
    congr 1
    rw [← LinearMap.comp_apply, ← TensorProduct.map_comp, LinearMap.id_comp]
    rfl

/-!

### A.3. The global gauge action on the target space

-/

/-- The global gauge action on the gauge-boson target space, the given action on the
  gauge-algebra factor and the trivial action on the spacetime index. -/
noncomputable def repValue {G₀ : Type} [Monoid G₀] (ρ : Representation ℝ G₀ G.lieSubalgebra) :
    Representation ℝ G₀ (GaugeBoson G) where
  toFun g := (valLinEquiv G).symm.toLinearMap ∘ₗ
    TensorProduct.map LinearMap.id (ρ g) ∘ₗ
    (valLinEquiv G).toLinearMap
  map_one' := by
    refine LinearMap.ext fun v => ?_
    simp [Module.End.one_eq_id]
  map_mul' g₁ g₂ := by
    refine LinearMap.ext fun v => ?_
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      mul_apply_eq_comp, LinearEquiv.apply_symm_apply, map_mul]
    congr 1
    rw [← LinearMap.comp_apply, ← TensorProduct.map_comp, LinearMap.id_comp]
    rfl

/-!

## B. The field-derivative space

-/

variable (G) in
/-- The field-derivative space of the gauge-boson field, the span of the component functions
  `∂_s A_μ^φ`. The `SpaceTimeDerivAlgebraℝ` factor carries the derivative label `s`, and the
  dual factor the spacetime and adjoint indices, the latter as an abstract covector on
  the gauge algebra with no basis chosen. Unlike a matter field, the gauge boson is real,
  so there is no conjugate half. -/
abbrev FieldDerivSpace : Type :=
  SpaceTimeDerivAlgebraℝ ⊗[ℝ] Module.Dual ℝ (GaugeBoson G)

/-!

### B.1. The component covectors

-/

variable (G) in
/-- The covector on the gauge-boson target space pairing the spacetime index against a
  covector `ω` and the adjoint index against `φ`. -/
noncomputable def componentDual :
    Module.Dual ℝ Lorentz.CoVector →ₗ[ℝ]
      Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] Module.Dual ℝ (GaugeBoson G) where
  toFun ω := (Module.Dual.transpose (M := (GaugeBoson G)) (valLinEquiv G).toLinearMap).comp
    ((TensorProduct.dualDistrib ℝ Lorentz.CoVector G.lieSubalgebra).comp
      (TensorProduct.mk ℝ (Module.Dual ℝ Lorentz.CoVector) (Module.Dual ℝ G.lieSubalgebra) ω))
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
    (φ : Module.Dual ℝ G.lieSubalgebra) (v : Lorentz.CoVector) (a : G.lieSubalgebra) :
    (componentDual G) ω φ ⟨v ⊗ₜ[ℝ] a⟩ = ω v * φ a := by
  simp [componentDual, Module.Dual.transpose_apply]

/-- Every covector on the gauge-boson target space decomposes along the Lorentz coordinate
  directions into component covectors. The spacetime index is expanded in the coordinate
  basis, while the adjoint index stays abstract. -/
lemma dual_eq_sum_componentDual
    (ψ : Module.Dual ℝ (GaugeBoson G)) :
    ψ = ∑ μ, (GaugeBoson.componentDual G) (Lorentz.CoVector.basis.dualBasis μ)
      (ψ ∘ₗ (GaugeBoson.valLinEquiv G).symm.toLinearMap ∘ₗ
        TensorProduct.mk ℝ Lorentz.CoVector G.lieSubalgebra (Lorentz.CoVector.basis μ)) := by
  refine LinearMap.ext fun v => ?_
  obtain ⟨m⟩ := v
  induction m using TensorProduct.inductionOn with
  | tmul x a =>
    rw [LinearMap.sum_apply]
    have hx : (⟨x ⊗ₜ[ℝ] a⟩ : (GaugeBoson G))
        = ∑ μ, Lorentz.CoVector.basis.dualBasis μ x •
            (⟨Lorentz.CoVector.basis μ ⊗ₜ[ℝ] a⟩ : (GaugeBoson G)) := by
      apply (GaugeBoson.valLinEquiv G).injective
      rw [map_sum]
      conv_lhs =>
        rw [GaugeBoson.valLinEquiv_apply,
          show (⟨x ⊗ₜ[ℝ] a⟩ : (GaugeBoson G)).val = x ⊗ₜ[ℝ] a from rfl,
          ← Lorentz.CoVector.basis.sum_repr x, TensorProduct.sum_tmul]
      refine Finset.sum_congr rfl fun μ _ => ?_
      rw [map_smul, GaugeBoson.valLinEquiv_apply,
        show (⟨Lorentz.CoVector.basis μ ⊗ₜ[ℝ] a⟩ : (GaugeBoson G)).val
          = Lorentz.CoVector.basis μ ⊗ₜ[ℝ] a from rfl, ← TensorProduct.smul_tmul',
        Module.Basis.dualBasis_apply]
    conv_lhs => rw [hx, map_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [map_smul, GaugeBoson.componentDual_apply_val_tmul, smul_eq_mul]
    rfl
  | add m₁ m₂ h₁ h₂ =>
    simp only [show (⟨m₁ + m₂⟩ : (GaugeBoson G)) = (⟨m₁⟩ : (GaugeBoson G)) + ⟨m₂⟩ from rfl,
      map_add, LinearMap.sum_apply] at h₁ h₂ ⊢
    rw [h₁, h₂, ← Finset.sum_add_distrib]

end GaugeBoson
