/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.ClassicalFieldTheory.GaugeTheory.GaugeJet
public import Physlib.Relativity.DerivAlgebra
public import Physlib.Mathematics.SymmetricAlgebra
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The jet algebra of the gauge bosons of a gauge theory

## i. Overview

The gauge bosons of a gauge theory with Lie algebra `𝔤` are jointly one bosonic field valued in
`Lorentz.CoVector ⊗[ℝ] GaugeAlgebra`: a spacetime covector with values in the gauge
algebra. Its *jet algebra* — the algebra in which the gauge-boson part of a Lagrangian
lives — is the free commutative algebra on the component functions `∂_s A_μ^φ` and is
built here in the same way as the `BBoson` jet algebra, but non-abelian and **without a
basis of the gauge algebra**: the adjoint index is carried by an abstract covector
`φ : Module.Dual ℝ GaugeAlgebra` throughout, following the dual-family formulation of
`Physlib.ClassicalFieldTheory.GaugeTheory.GaugeField`. For the Standard Model, `𝔤` is
`GaugeAlgebra`; see `Physlib.Particles.StandardModel.GaugeBosons.GaugeJetAlgebra.Basic`.

Following the split promised for this directory, the structure is:
1. this file — the target space, the jet component space, and the jet algebra with its
   generators;
2. `LorentzAction` — the action of the Lorentz group;
3. `GaugeAction` — the action of the jet gauge group;
4. `JetDeriv` — the formal total derivative;
5. `MassDim` — the mass-dimension grading.

## ii. Key results

- `GaugeBoson` : the target space of the gauge-boson field.
- `GaugeBoson.repLorentzGroup` : the Lorentz action on the target space.
- `GaugeBoson.repGaugeGroupI` : the global (adjoint) gauge action on the target space.
- `GaugeBoson.JetComponentSpace` : the span of the component functions `∂_s A_μ^φ`.
- `GaugeJetAlgebra` : the jet algebra of the gauge bosons.
- `GaugeJetAlgebra.ofComponent`, `GaugeJetAlgebra.ofA` : the generators.

## iii. Table of contents

- A. The target space of the gauge-boson field
  - A.1. Linear structure
  - A.2. The Lorentz action on the target space
  - A.3. The global gauge action on the target space
- B. The jet component space
  - B.1. The component covectors
- C. The jet algebra
  - C.1. The generators

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
    simp [TensorProduct.add_tmul]
  map_smul' r ω := by
    refine LinearMap.ext fun φ => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, TensorProduct.mk_apply,
      RingHom.id_apply, LinearMap.smul_apply]
    rw [← TensorProduct.smul_tmul', map_smul, map_smul]

@[simp]
lemma componentDual_apply_val_tmul (ω : Module.Dual ℝ Lorentz.CoVector)
    (φ : Module.Dual ℝ 𝔤) (v : Lorentz.CoVector) (a : 𝔤) :
    (componentDual 𝔤) ω φ ⟨v ⊗ₜ[ℝ] a⟩ = ω v * φ a := by
  simp [componentDual, Module.Dual.transpose_apply, valLinEquiv_symm_apply]

end GaugeBoson

/-!

## C. The jet algebra

-/

variable (𝔤) in
/-- **The jet algebra of the gauge bosons**: the free commutative algebra
  on the component functions `∂_s A_μ^φ` of the gauge-boson field, realized as the
  symmetric algebra on the jet component space. The commutativity of the product is the
  Bose statistics of the gauge fields. -/
abbrev GaugeJetAlgebra : Type := SymmetricAlgebra ℝ (GaugeBoson.JetComponentSpace 𝔤)

namespace GaugeJetAlgebra

/-!

### C.1. The generators

-/

variable (𝔤) in
/-- The undifferentiated component function `A^φ` of the gauge-boson field along a
  covector `φ` on the target space. -/
noncomputable def ofComponent : Module.Dual ℝ (GaugeBoson 𝔤) →ₗ[ℝ] (GaugeJetAlgebra 𝔤) :=
  (SymmetricAlgebra.ι ℝ _).comp
    (TensorProduct.mk ℝ DerivAlgebraReal (Module.Dual ℝ (GaugeBoson 𝔤)) 1)

lemma ofComponent_apply (φ : Module.Dual ℝ (GaugeBoson 𝔤)) :
    (ofComponent 𝔤) φ = SymmetricAlgebra.ι ℝ _ ((1 : DerivAlgebraReal) ⊗ₜ[ℝ] φ) := rfl

variable (𝔤) in
/-- **The component function `A_μ^φ` of the gauge-boson field**: the spacetime index `μ`
  paired against the Lorentz coordinate basis, the adjoint index against the abstract
  covector `φ` on the gauge algebra. These are the generators the ambient theory sees;
  no basis of the gauge algebra is involved. -/
noncomputable def ofA (μ : Fin 1 ⊕ Fin 3) :
    Module.Dual ℝ 𝔤 →ₗ[ℝ] (GaugeJetAlgebra 𝔤) :=
  (ofComponent 𝔤).comp ((GaugeBoson.componentDual 𝔤) (Lorentz.CoVector.basis.dualBasis μ))

lemma ofA_apply (μ : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ 𝔤) :
    (ofA 𝔤) μ φ = (ofComponent 𝔤) ((GaugeBoson.componentDual 𝔤)
      (Lorentz.CoVector.basis.dualBasis μ) φ) := rfl

/-- The jet algebra is generated by the component functions. -/
@[simp]
lemma adjoin_ι_eq_top :
    Algebra.adjoin ℝ (Set.range (SymmetricAlgebra.ι ℝ (GaugeBoson.JetComponentSpace 𝔤))) = ⊤ :=
  SymmetricAlgebra.adjoin_range_ι

end GaugeJetAlgebra

