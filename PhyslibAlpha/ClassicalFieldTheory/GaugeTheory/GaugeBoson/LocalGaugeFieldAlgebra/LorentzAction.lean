/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.GaugeBoson.LocalGaugeFieldAlgebra.JetDeriv
public import PhyslibAlpha.Relativity.IsLorentzDeriv

/-!
# The Lorentz action on the gauge-boson jet algebra

The action of `SL(2,ℂ)` on the gauge-boson jet algebra, for which the total derivative is a
Lorentz vector.

## i. Overview

The Lorentz group acts on the jet algebra of the gauge bosons by the symmetric-algebra
functor applied to its action on the field-derivative space. The derivative labels transform
in `SpaceTimeDerivAlgebraℝ` and the target index contragrediently through the covector action on
`GaugeBoson`. The formal total derivative is a Lorentz vector for this action. On the
complexification this is packaged as a `Lorentz.IsLorentzDeriv` instance.

## ii. Key results

- `GaugeBoson.FieldDerivSpace.repLorentzGroup` : the Lorentz action on the component
  space.
- `LocalGaugeFieldAlgebra.repLorentzGroup` : the Lorentz action on the jet algebra.
- `LocalGaugeFieldAlgebra.repLorentzGroup_jetDeriv` : the total derivative is a Lorentz vector.
- `LocalGaugeFieldAlgebra.complexRepLorentzGroup` : the action on the complexification.
- `LocalGaugeFieldAlgebra.instIsLorentzDeriv` : the `Lorentz.IsLorentzDeriv` instance.

## iii. Table of contents

- A. The Lorentz action on the component space
  - A.1. Covariance of the derivative shift
- B. The Lorentz action on the jet algebra
- C. Lorentz covariance of the total derivative
- D. The complexified action
- E. The Lorentz law of the gauge-field generators

## iv. References

* None.

-/

@[expose] public section

set_option linter.unusedSectionVars false

variable {κ : Type} [Fintype κ] [DecidableEq κ] {G : GlobalGaugeGroup κ}


open TensorProduct Matrix MatrixGroups

/-!

## A. The Lorentz action on the component space

-/

namespace GaugeBoson

variable (G) in
/-- The Lorentz action on the field-derivative space of the gauge bosons. The derivative
  label transforms in `SpaceTimeDerivAlgebraℝ` and the target index contragrediently. -/
noncomputable def FieldDerivSpace.repLorentzGroup :
    Representation ℝ SL(2,ℂ) (FieldDerivSpace G) :=
  SpaceTimeDerivAlgebraℝ.repLorentzGroup.tprod (GaugeBoson.repLorentzGroup G).dual

/-!

### A.1. Covariance of the derivative shift

-/

/-- The Lorentz action on the singleton derivative symbol. The derivative slot transforms
  by the columns of the Lorentz matrix. -/
lemma _root_.SpaceTimeDerivAlgebraℝ.repLorentzGroup_basis_singleton
    (Λ : SL(2,ℂ)) (μ : Fin 1 ⊕ Fin 3) :
    SpaceTimeDerivAlgebraℝ.repLorentzGroup Λ
        (SpaceTimeDerivAlgebraℝ.basisMultiset ({μ} : Multiset (Fin 1 ⊕ Fin 3))) =
      ∑ a, ((Lorentz.SL2C.toLorentzGroup Λ).1 a μ) •
        SpaceTimeDerivAlgebraℝ.basisMultiset ({a} : Multiset (Fin 1 ⊕ Fin 3)) := by
  rw [SpaceTimeDerivAlgebraℝ.basisMultiset_singleton,
    SpaceTimeDerivAlgebraℝ.repLorentzGroup_apply_ι, Lorentz.CoVector.sl2Rep_dual_dualBasis,
    map_sum]
  exact Finset.sum_congr rfl fun a _ => by
    rw [map_smul, SpaceTimeDerivAlgebraℝ.basisMultiset_singleton]

/-- The derivative shift is a Lorentz vector on the component space. Appending `∂_μ`
  and then acting is acting and then appending the transformed `∂_μ`. -/
lemma FieldDerivSpace.repLorentzGroup_jetDeriv (Λ : SL(2,ℂ)) (μ : Fin 1 ⊕ Fin 3)
    (v : (FieldDerivSpace G)) :
    (FieldDerivSpace.repLorentzGroup G) Λ ((FieldDerivSpace.jetDeriv G) μ v) =
      ∑ a, ((Lorentz.SL2C.toLorentzGroup Λ).1 a μ) •
        (FieldDerivSpace.jetDeriv G) a ((FieldDerivSpace.repLorentzGroup G) Λ v) := by
  induction v using TensorProduct.inductionOn with
  | add x y hx hy =>
    rw [map_add, map_add, map_add, hx, hy, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => by rw [map_add, smul_add]
  | tmul q f =>
    rw [FieldDerivSpace.jetDeriv_tmul,
      show (FieldDerivSpace.repLorentzGroup G) Λ
          ((q * SpaceTimeDerivAlgebraℝ.basisMultiset
            ({μ} : Multiset (Fin 1 ⊕ Fin 3))) ⊗ₜ[ℝ] f)
        = (SpaceTimeDerivAlgebraℝ.repLorentzGroup Λ
            (q * SpaceTimeDerivAlgebraℝ.basisMultiset
              ({μ} : Multiset (Fin 1 ⊕ Fin 3)))) ⊗ₜ[ℝ]
          ((GaugeBoson.repLorentzGroup G).dual Λ f) from rfl,
      SpaceTimeDerivAlgebraℝ.repLorentzGroup_apply_mul,
      SpaceTimeDerivAlgebraℝ.repLorentzGroup_basis_singleton, Finset.mul_sum,
      TensorProduct.sum_tmul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [mul_smul_comm, ← TensorProduct.smul_tmul',
      show (FieldDerivSpace.repLorentzGroup G) Λ (q ⊗ₜ[ℝ] f)
        = (SpaceTimeDerivAlgebraℝ.repLorentzGroup Λ q) ⊗ₜ[ℝ]
          ((GaugeBoson.repLorentzGroup G).dual Λ f) from rfl,
      FieldDerivSpace.jetDeriv_tmul]

end GaugeBoson

namespace LocalGaugeFieldAlgebra

/-!

## B. The Lorentz action on the jet algebra

-/

variable (G) in
/-- The Lorentz action on the gauge-boson jet algebra, the symmetric-algebra functor
  applied to the Lorentz action on the field-derivative space. -/
noncomputable def repLorentzGroup : Representation ℝ SL(2,ℂ) (LocalGaugeFieldAlgebra G) where
  toFun Λ :=
    (SymmetricAlgebra.map ((GaugeBoson.FieldDerivSpace.repLorentzGroup G) Λ)).toLinearMap
  map_one' := by
    simp only [map_one, Module.End.one_eq_id, SymmetricAlgebra.map_id, AlgHom.toLinearMap_id]
  map_mul' Λ₁ Λ₂ := by
    simp only [map_mul, Module.End.mul_eq_comp, ← SymmetricAlgebra.map_comp_map,
      AlgHom.comp_toLinearMap]

lemma repLorentzGroup_apply (Λ : SL(2,ℂ)) (x : (LocalGaugeFieldAlgebra G)) :
    (repLorentzGroup G) Λ x =
      SymmetricAlgebra.map ((GaugeBoson.FieldDerivSpace.repLorentzGroup G) Λ) x := rfl

@[simp]
lemma repLorentzGroup_apply_one (Λ : SL(2,ℂ)) :
    (repLorentzGroup G) Λ (1 : (LocalGaugeFieldAlgebra G)) = 1 := by
  simp [repLorentzGroup_apply]

lemma repLorentzGroup_apply_mul (Λ : SL(2,ℂ)) (x y : (LocalGaugeFieldAlgebra G)) :
    (repLorentzGroup G) Λ (x * y) = (repLorentzGroup G) Λ x * (repLorentzGroup G) Λ y := by
  simp [repLorentzGroup_apply]

@[simp]
lemma repLorentzGroup_ι (Λ : SL(2,ℂ)) (v : (GaugeBoson.FieldDerivSpace G)) :
    (repLorentzGroup G) Λ (SymmetricAlgebra.ι ℝ _ v) =
      SymmetricAlgebra.ι ℝ _ ((GaugeBoson.FieldDerivSpace.repLorentzGroup G) Λ v) := by
  rw [repLorentzGroup_apply, SymmetricAlgebra.map_apply_ι]

/-!

## C. Lorentz covariance of the total derivative

-/

/-- The total derivative on the gauge-boson jet algebra is a Lorentz vector. -/
lemma repLorentzGroup_jetDeriv (Λ : SL(2,ℂ)) (μ : Fin 1 ⊕ Fin 3) (x : (LocalGaugeFieldAlgebra G)) :
    (repLorentzGroup G) Λ ((jetDeriv G) μ x) =
      ∑ a, ((Lorentz.SL2C.toLorentzGroup Λ).1 a μ) •
        (jetDeriv G) a ((repLorentzGroup G) Λ x) := by
  induction x using SymmetricAlgebra.induction with
  | algebraMap r =>
    rw [jetDeriv_algebraMap, map_zero]
    refine (Finset.sum_eq_zero fun a _ => ?_).symm
    rw [Algebra.algebraMap_eq_smul_one, map_smul, repLorentzGroup_apply_one, map_smul,
      jetDeriv_one, smul_zero, smul_zero]
  | ι v =>
    rw [jetDeriv_ι, repLorentzGroup_ι, repLorentzGroup_ι,
      GaugeBoson.FieldDerivSpace.repLorentzGroup_jetDeriv, map_sum]
    exact Finset.sum_congr rfl fun a _ => by rw [map_smul, jetDeriv_ι]
  | mul a b ha hb =>
    rw [jetDeriv_mul, map_add, repLorentzGroup_apply_mul, repLorentzGroup_apply_mul, ha, hb,
      Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib, repLorentzGroup_apply_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [jetDeriv_mul, smul_add, smul_mul_assoc, mul_smul_comm]
  | add a b ha hb =>
    rw [map_add, map_add, map_add, ha, hb, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => by rw [map_add, smul_add]

/-!

## D. The complexified action

-/

variable (G) in
/-- The Lorentz action on the complexified gauge-boson jet algebra, by base change. -/
noncomputable def complexRepLorentzGroup :
    Representation ℂ SL(2,ℂ) (ℂ ⊗[ℝ] (LocalGaugeFieldAlgebra G)) where
  toFun Λ := LinearMap.baseChange ℂ ((repLorentzGroup G) Λ)
  map_one' := by
    rw [map_one, Module.End.one_eq_id, LinearMap.baseChange_id, Module.End.one_eq_id]
  map_mul' Λ₁ Λ₂ := by
    rw [map_mul, Module.End.mul_eq_comp, LinearMap.baseChange_comp, Module.End.mul_eq_comp]

@[simp]
lemma complexRepLorentzGroup_tmul (Λ : SL(2,ℂ)) (z : ℂ) (x : (LocalGaugeFieldAlgebra G)) :
    (complexRepLorentzGroup G) Λ (z ⊗ₜ[ℝ] x) = z ⊗ₜ[ℝ] (repLorentzGroup G) Λ x := rfl

variable (G) in
/-- The action of a Lorentz transformation on the complexified gauge-boson jet algebra, as
  an algebra endomorphism, the base change of the symmetric-algebra functor applied to the
  action on the field-derivative space. -/
noncomputable def complexRepLorentzGroupAlgHom (Λ : SL(2,ℂ)) :
    ℂ ⊗[ℝ] (LocalGaugeFieldAlgebra G) →ₐ[ℂ] ℂ ⊗[ℝ] (LocalGaugeFieldAlgebra G) :=
  Algebra.TensorProduct.map (AlgHom.id ℂ ℂ)
    (SymmetricAlgebra.map ((GaugeBoson.FieldDerivSpace.repLorentzGroup G) Λ))

lemma complexRepLorentzGroup_apply (Λ : SL(2,ℂ)) (x : ℂ ⊗[ℝ] (LocalGaugeFieldAlgebra G)) :
    (complexRepLorentzGroup G) Λ x = complexRepLorentzGroupAlgHom G Λ x := by
  induction x using TensorProduct.inductionOn with
  | add x₁ x₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂]
  | tmul z a => rfl

lemma complexRepLorentzGroup_apply_mul (Λ : SL(2,ℂ)) (x y : ℂ ⊗[ℝ] (LocalGaugeFieldAlgebra G)) :
    (complexRepLorentzGroup G) Λ (x * y)
      = (complexRepLorentzGroup G) Λ x * (complexRepLorentzGroup G) Λ y := by
  induction x using TensorProduct.inductionOn with
  | add x₁ x₂ h₁ h₂ => rw [add_mul, map_add, map_add, h₁, h₂, add_mul]
  | tmul z₁ a₁ =>
    induction y using TensorProduct.inductionOn with
    | add y₁ y₂ h₁ h₂ => rw [mul_add, map_add, map_add, h₁, h₂, mul_add]
    | tmul z₂ a₂ =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, complexRepLorentzGroup_tmul,
        complexRepLorentzGroup_tmul, complexRepLorentzGroup_tmul,
        repLorentzGroup_apply_mul, Algebra.TensorProduct.tmul_mul_tmul]

/-- The complexified total derivative is a Lorentz vector. -/
lemma complexRepLorentzGroup_jetDeriv (Λ : SL(2,ℂ)) (μ : Fin 1 ⊕ Fin 3)
    (x : ℂ ⊗[ℝ] (LocalGaugeFieldAlgebra G)) :
    (complexRepLorentzGroup G) Λ ((complexJetDeriv G) μ x) =
      ∑ a, (((Lorentz.SL2C.toLorentzGroup Λ).1 a μ : ℝ) : ℂ) •
        (complexJetDeriv G) a ((complexRepLorentzGroup G) Λ x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy =>
    rw [map_add, map_add, map_add, hx, hy, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => by rw [map_add, smul_add]
  | tmul z a =>
    rw [complexJetDeriv_tmul, complexRepLorentzGroup_tmul, repLorentzGroup_jetDeriv,
      TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [TensorProduct.tmul_smul, complexRepLorentzGroup_tmul, complexJetDeriv_tmul,
      show ((((Lorentz.SL2C.toLorentzGroup Λ).1 c μ : ℝ)) : ℂ)
        = algebraMap ℝ ℂ ((Lorentz.SL2C.toLorentzGroup Λ).1 c μ) from rfl,
      algebraMap_smul]

/-- The complexified total derivatives form a Lorentz derivative, a family of derivatives
  transforming as a Lorentz vector. -/
instance instIsLorentzDeriv :
    Lorentz.IsLorentzDeriv (complexRepLorentzGroup G) (complexJetDeriv G) where
  rep_deriv := complexRepLorentzGroup_jetDeriv _ _ _

/-!

## E. The Lorentz law of the gauge-field generators

-/

/-- The contragredient Lorentz action passes through a component covector to its spacetime
  slot. The adjoint index is Lorentz-inert. -/
lemma _root_.GaugeBoson.repLorentzGroup_dual_componentDual (Λ : SL(2,ℂ))
    (ω : Module.Dual ℝ Lorentz.CoVector) (φ : Module.Dual ℝ G.lieSubalgebra) :
    (GaugeBoson.repLorentzGroup G).dual Λ ((GaugeBoson.componentDual G) ω φ)
      = (GaugeBoson.componentDual G) (Lorentz.CoVector.sl2Rep.dual Λ ω) φ := by
  refine LinearMap.ext fun v => ?_
  obtain ⟨m⟩ := v
  induction m using TensorProduct.inductionOn with
  | tmul x a =>
    rw [Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply,
      show (GaugeBoson.repLorentzGroup G) Λ⁻¹ (⟨x ⊗ₜ[ℝ] a⟩ : (GaugeBoson G))
        = ⟨(Lorentz.CoVector.sl2Rep Λ⁻¹ x) ⊗ₜ[ℝ] a⟩ from rfl,
      GaugeBoson.componentDual_apply_val_tmul, GaugeBoson.componentDual_apply_val_tmul,
      Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply]
  | add m₁ m₂ h₁ h₂ =>
    rw [show (⟨m₁ + m₂⟩ : (GaugeBoson G)) = (⟨m₁⟩ : (GaugeBoson G)) + ⟨m₂⟩ from rfl, map_add,
      map_add, h₁, h₂]

/-- The gauge field is a Lorentz covector. The generator `A_μ^φ` mixes into the `A_a^φ`
  by the columns of the Lorentz matrix, with the adjoint index untouched. -/
lemma repLorentzGroup_ofA (Λ : SL(2,ℂ)) (μ : Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℝ G.lieSubalgebra) :
    (repLorentzGroup G) Λ ((ofA G) μ φ)
      = ∑ a, ((Lorentz.SL2C.toLorentzGroup Λ).1 a μ) • (ofA G) a φ := by
  rw [ofA_apply, ofComponent_apply, repLorentzGroup_ι,
    show (GaugeBoson.FieldDerivSpace.repLorentzGroup G) Λ
        ((1 : SpaceTimeDerivAlgebraℝ) ⊗ₜ[ℝ] (GaugeBoson.componentDual G)
          (Lorentz.CoVector.basis.dualBasis μ) φ)
      = (SpaceTimeDerivAlgebraℝ.repLorentzGroup Λ (1 : SpaceTimeDerivAlgebraℝ)) ⊗ₜ[ℝ]
        ((GaugeBoson.repLorentzGroup G).dual Λ ((GaugeBoson.componentDual G)
          (Lorentz.CoVector.basis.dualBasis μ) φ)) from rfl,
    SpaceTimeDerivAlgebraℝ.repLorentzGroup_apply_one,
    GaugeBoson.repLorentzGroup_dual_componentDual,
    Lorentz.CoVector.sl2Rep_dual_dualBasis, map_sum, LinearMap.sum_apply,
    TensorProduct.tmul_sum, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_smul, LinearMap.smul_apply, TensorProduct.tmul_smul, map_smul, ofA_apply,
    ofComponent_apply]

/-- The Lorentz law of the gauge-field generators on the complexification. -/
lemma complexRepLorentzGroup_one_tmul_ofA (Λ : SL(2,ℂ)) (μ : Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℝ G.lieSubalgebra) :
    (complexRepLorentzGroup G) Λ ((1 : ℂ) ⊗ₜ[ℝ] (ofA G) μ φ)
      = ∑ a, (((Lorentz.SL2C.toLorentzGroup Λ).1 a μ : ℝ) : ℂ) •
          ((1 : ℂ) ⊗ₜ[ℝ] (ofA G) a φ) := by
  rw [complexRepLorentzGroup_tmul, repLorentzGroup_ofA, TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [TensorProduct.tmul_smul,
    show ((((Lorentz.SL2C.toLorentzGroup Λ).1 a μ : ℝ)) : ℂ)
      = algebraMap ℝ ℂ ((Lorentz.SL2C.toLorentzGroup Λ).1 a μ) from rfl,
    algebraMap_smul]

end LocalGaugeFieldAlgebra

