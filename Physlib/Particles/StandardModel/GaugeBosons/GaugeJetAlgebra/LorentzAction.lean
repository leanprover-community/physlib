/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.GaugeBosons.GaugeJetAlgebra.JetDeriv
public import Physlib.Relativity.IsLorentzDeriv
/-!
# The Lorentz action on the gauge-boson jet algebra

## i. Overview

The Lorentz group acts on the jet algebra of the gauge bosons by the symmetric-algebra
functor applied to its action on the jet component space: the derivative labels transform
in `DerivAlgebraReal` and the target index contragrediently through the covector action on
`GaugeBoson`. The formal total derivative is a Lorentz vector for this action; on the
complexification this is packaged as a `Lorentz.IsLorentzDeriv` instance, giving access to
the boost-weight machinery.

## ii. Key results

- `GaugeBoson.JetComponentSpace.repLorentzGroup` : the Lorentz action on the component
  space.
- `GaugeJetAlgebra.repLorentzGroup` : the Lorentz action on the jet algebra.
- `GaugeJetAlgebra.repLorentzGroup_jetDeriv` : the total derivative is a Lorentz vector.
- `GaugeJetAlgebra.complexRepLorentzGroup` : the action on the complexification.
- `GaugeJetAlgebra.instIsLorentzDeriv` : the `Lorentz.IsLorentzDeriv` instance.

## iii. Table of contents

- A. The Lorentz action on the component space
  - A.1. Covariance of the derivative shift
- B. The Lorentz action on the jet algebra
- C. Lorentz covariance of the total derivative
- D. The complexified action

-/

@[expose] public section

set_option maxHeartbeats 1000000

namespace StandardModel

open TensorProduct Matrix MatrixGroups

/-!

## A. The Lorentz action on the component space

-/

namespace GaugeBoson

/-- The Lorentz action on the jet component space of the gauge bosons: the derivative
  label transforms in `DerivAlgebraReal`, the target index contragrediently. -/
noncomputable def JetComponentSpace.repLorentzGroup :
    Representation ℝ SL(2,ℂ) JetComponentSpace :=
  DerivAlgebraReal.repLorentzGroup.tprod GaugeBoson.repLorentzGroup.dual

/-!

### A.1. Covariance of the derivative shift

-/

/-- The Lorentz action on the singleton derivative symbol: the derivative slot transforms
  by the columns of the Lorentz matrix. -/
lemma _root_.StandardModel.DerivAlgebraReal.repLorentzGroup_basis_singleton
    (Λ : SL(2,ℂ)) (μ : Fin 1 ⊕ Fin 3) :
    DerivAlgebraReal.repLorentzGroup Λ
        (LagrangianTheory.dualRealJetAlgebraBasis ({μ} : Multiset (Fin 1 ⊕ Fin 3))) =
      ∑ a, ((Lorentz.SL2C.toLorentzGroup Λ).1 a μ) •
        LagrangianTheory.dualRealJetAlgebraBasis ({a} : Multiset (Fin 1 ⊕ Fin 3)) := by
  rw [LagrangianTheory.dualRealJetAlgebraBasis_singleton,
    DerivAlgebraReal.repLorentzGroup_apply_ι, Lorentz.CoVector.sl2Rep_dual_dualBasis,
    map_sum]
  exact Finset.sum_congr rfl fun a _ => by
    rw [map_smul, LagrangianTheory.dualRealJetAlgebraBasis_singleton]

/-- **The derivative shift is a Lorentz vector on the component space**: appending `∂_μ`
  and then acting is acting and then appending the transformed `∂_μ`. -/
lemma JetComponentSpace.repLorentzGroup_jetDeriv (Λ : SL(2,ℂ)) (μ : Fin 1 ⊕ Fin 3)
    (v : JetComponentSpace) :
    JetComponentSpace.repLorentzGroup Λ (JetComponentSpace.jetDeriv μ v) =
      ∑ a, ((Lorentz.SL2C.toLorentzGroup Λ).1 a μ) •
        JetComponentSpace.jetDeriv a (JetComponentSpace.repLorentzGroup Λ v) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
    rw [map_add, map_add, map_add, hx, hy, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => by rw [map_add, smul_add]
  | tmul q f =>
    rw [JetComponentSpace.jetDeriv_tmul,
      show JetComponentSpace.repLorentzGroup Λ
          ((q * LagrangianTheory.dualRealJetAlgebraBasis
            ({μ} : Multiset (Fin 1 ⊕ Fin 3))) ⊗ₜ[ℝ] f)
        = (DerivAlgebraReal.repLorentzGroup Λ
            (q * LagrangianTheory.dualRealJetAlgebraBasis
              ({μ} : Multiset (Fin 1 ⊕ Fin 3)))) ⊗ₜ[ℝ]
          (GaugeBoson.repLorentzGroup.dual Λ f) from rfl,
      DerivAlgebraReal.repLorentzGroup_apply_mul,
      DerivAlgebraReal.repLorentzGroup_basis_singleton, Finset.mul_sum,
      TensorProduct.sum_tmul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [mul_smul_comm, ← TensorProduct.smul_tmul',
      show JetComponentSpace.repLorentzGroup Λ (q ⊗ₜ[ℝ] f)
        = (DerivAlgebraReal.repLorentzGroup Λ q) ⊗ₜ[ℝ]
          (GaugeBoson.repLorentzGroup.dual Λ f) from rfl,
      JetComponentSpace.jetDeriv_tmul]

end GaugeBoson

namespace GaugeJetAlgebra

/-!

## B. The Lorentz action on the jet algebra

-/

/-- **The Lorentz action on the gauge-boson jet algebra**: the symmetric-algebra functor
  applied to the Lorentz action on the jet component space. -/
noncomputable def repLorentzGroup : Representation ℝ SL(2,ℂ) GaugeJetAlgebra where
  toFun Λ :=
    (SymmetricAlgebra.map (GaugeBoson.JetComponentSpace.repLorentzGroup Λ)).toLinearMap
  map_one' := by
    simp only [map_one, Module.End.one_eq_id, SymmetricAlgebra.map_id, AlgHom.toLinearMap_id]
  map_mul' Λ₁ Λ₂ := by
    simp only [map_mul, Module.End.mul_eq_comp, ← SymmetricAlgebra.map_comp_map,
      AlgHom.comp_toLinearMap]

lemma repLorentzGroup_apply (Λ : SL(2,ℂ)) (x : GaugeJetAlgebra) :
    repLorentzGroup Λ x =
      SymmetricAlgebra.map (GaugeBoson.JetComponentSpace.repLorentzGroup Λ) x := rfl

@[simp]
lemma repLorentzGroup_apply_one (Λ : SL(2,ℂ)) :
    repLorentzGroup Λ (1 : GaugeJetAlgebra) = 1 := by
  simp [repLorentzGroup_apply]

lemma repLorentzGroup_apply_mul (Λ : SL(2,ℂ)) (x y : GaugeJetAlgebra) :
    repLorentzGroup Λ (x * y) = repLorentzGroup Λ x * repLorentzGroup Λ y := by
  simp [repLorentzGroup_apply]

@[simp]
lemma repLorentzGroup_ι (Λ : SL(2,ℂ)) (v : GaugeBoson.JetComponentSpace) :
    repLorentzGroup Λ (SymmetricAlgebra.ι ℝ _ v) =
      SymmetricAlgebra.ι ℝ _ (GaugeBoson.JetComponentSpace.repLorentzGroup Λ v) := by
  rw [repLorentzGroup_apply, SymmetricAlgebra.map_apply_ι]

/-!

## C. Lorentz covariance of the total derivative

-/

/-- **The total derivative on the gauge-boson jet algebra is a Lorentz vector.** -/
lemma repLorentzGroup_jetDeriv (Λ : SL(2,ℂ)) (μ : Fin 1 ⊕ Fin 3) (x : GaugeJetAlgebra) :
    repLorentzGroup Λ (jetDeriv μ x) =
      ∑ a, ((Lorentz.SL2C.toLorentzGroup Λ).1 a μ) •
        jetDeriv a (repLorentzGroup Λ x) := by
  induction x using SymmetricAlgebra.induction with
  | algebraMap r =>
    rw [jetDeriv_algebraMap, map_zero]
    refine (Finset.sum_eq_zero fun a _ => ?_).symm
    rw [Algebra.algebraMap_eq_smul_one, map_smul, repLorentzGroup_apply_one, map_smul,
      jetDeriv_one, smul_zero, smul_zero]
  | ι v =>
    rw [jetDeriv_ι, repLorentzGroup_ι, repLorentzGroup_ι,
      GaugeBoson.JetComponentSpace.repLorentzGroup_jetDeriv, map_sum]
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

/-- The Lorentz action on the complexified gauge-boson jet algebra, by base change. -/
noncomputable def complexRepLorentzGroup :
    Representation ℂ SL(2,ℂ) (ℂ ⊗[ℝ] GaugeJetAlgebra) where
  toFun Λ := LinearMap.baseChange ℂ (repLorentzGroup Λ)
  map_one' := by
    rw [map_one, Module.End.one_eq_id, LinearMap.baseChange_id, Module.End.one_eq_id]
  map_mul' Λ₁ Λ₂ := by
    rw [map_mul, Module.End.mul_eq_comp, LinearMap.baseChange_comp, Module.End.mul_eq_comp]

@[simp]
lemma complexRepLorentzGroup_tmul (Λ : SL(2,ℂ)) (z : ℂ) (x : GaugeJetAlgebra) :
    complexRepLorentzGroup Λ (z ⊗ₜ[ℝ] x) = z ⊗ₜ[ℝ] repLorentzGroup Λ x := rfl

lemma complexRepLorentzGroup_apply_mul (Λ : SL(2,ℂ)) (x y : ℂ ⊗[ℝ] GaugeJetAlgebra) :
    complexRepLorentzGroup Λ (x * y)
      = complexRepLorentzGroup Λ x * complexRepLorentzGroup Λ y := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x₁ x₂ h₁ h₂ => rw [add_mul, map_add, map_add, h₁, h₂, add_mul]
  | tmul z₁ a₁ =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y₁ y₂ h₁ h₂ => rw [mul_add, map_add, map_add, h₁, h₂, mul_add]
    | tmul z₂ a₂ =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, complexRepLorentzGroup_tmul,
        complexRepLorentzGroup_tmul, complexRepLorentzGroup_tmul,
        repLorentzGroup_apply_mul, Algebra.TensorProduct.tmul_mul_tmul]

/-- **The complexified total derivative is a Lorentz vector.** -/
lemma complexRepLorentzGroup_jetDeriv (Λ : SL(2,ℂ)) (μ : Fin 1 ⊕ Fin 3)
    (x : ℂ ⊗[ℝ] GaugeJetAlgebra) :
    complexRepLorentzGroup Λ (complexJetDeriv μ x) =
      ∑ a, (((Lorentz.SL2C.toLorentzGroup Λ).1 a μ : ℝ) : ℂ) •
        complexJetDeriv a (complexRepLorentzGroup Λ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
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

/-- The complexified total derivatives form a Lorentz derivative, giving access to the
  boost-weight machinery. -/
instance instIsLorentzDeriv :
    Lorentz.IsLorentzDeriv complexRepLorentzGroup complexJetDeriv where
  rep_deriv := complexRepLorentzGroup_jetDeriv _ _ _

/-!

## E. The Lorentz law of the gauge-field generators

-/

/-- The contragredient Lorentz action passes through a component covector to its spacetime
  slot: the adjoint index is Lorentz-inert. -/
lemma _root_.StandardModel.GaugeBoson.repLorentzGroup_dual_componentDual (Λ : SL(2,ℂ))
    (ω : Module.Dual ℝ Lorentz.CoVector) (φ : Module.Dual ℝ GaugeAlgebra) :
    GaugeBoson.repLorentzGroup.dual Λ (GaugeBoson.componentDual ω φ)
      = GaugeBoson.componentDual (Lorentz.CoVector.sl2Rep.dual Λ ω) φ := by
  refine LinearMap.ext fun v => ?_
  obtain ⟨m⟩ := v
  induction m using TensorProduct.induction_on with
  | zero =>
    rw [show (⟨0⟩ : GaugeBoson) = 0 from rfl, map_zero, map_zero]
  | tmul x a =>
    rw [Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply,
      show GaugeBoson.repLorentzGroup Λ⁻¹ (⟨x ⊗ₜ[ℝ] a⟩ : GaugeBoson)
        = ⟨(Lorentz.CoVector.sl2Rep Λ⁻¹ x) ⊗ₜ[ℝ] a⟩ from rfl,
      GaugeBoson.componentDual_apply_val_tmul, GaugeBoson.componentDual_apply_val_tmul,
      Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply]
  | add m₁ m₂ h₁ h₂ =>
    rw [show (⟨m₁ + m₂⟩ : GaugeBoson) = (⟨m₁⟩ : GaugeBoson) + ⟨m₂⟩ from rfl, map_add,
      map_add, h₁, h₂]

/-- **The gauge field is a Lorentz covector**: the generator `A_μ^φ` mixes into the `A_a^φ`
  by the columns of the Lorentz matrix, with the adjoint index untouched. -/
lemma repLorentzGroup_ofA (Λ : SL(2,ℂ)) (μ : Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℝ GaugeAlgebra) :
    repLorentzGroup Λ (ofA μ φ)
      = ∑ a, ((Lorentz.SL2C.toLorentzGroup Λ).1 a μ) • ofA a φ := by
  rw [ofA_apply, ofComponent_apply, repLorentzGroup_ι,
    show GaugeBoson.JetComponentSpace.repLorentzGroup Λ
        ((1 : DerivAlgebraReal) ⊗ₜ[ℝ] GaugeBoson.componentDual
          (Lorentz.CoVector.basis.dualBasis μ) φ)
      = (DerivAlgebraReal.repLorentzGroup Λ (1 : DerivAlgebraReal)) ⊗ₜ[ℝ]
        (GaugeBoson.repLorentzGroup.dual Λ (GaugeBoson.componentDual
          (Lorentz.CoVector.basis.dualBasis μ) φ)) from rfl,
    DerivAlgebraReal.repLorentzGroup_apply_one,
    GaugeBoson.repLorentzGroup_dual_componentDual,
    Lorentz.CoVector.sl2Rep_dual_dualBasis, map_sum, LinearMap.sum_apply,
    TensorProduct.tmul_sum, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_smul, LinearMap.smul_apply, TensorProduct.tmul_smul, map_smul, ofA_apply,
    ofComponent_apply]

/-- The Lorentz law of the gauge-field generators on the complexification. -/
lemma complexRepLorentzGroup_one_tmul_ofA (Λ : SL(2,ℂ)) (μ : Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℝ GaugeAlgebra) :
    complexRepLorentzGroup Λ ((1 : ℂ) ⊗ₜ[ℝ] ofA μ φ)
      = ∑ a, (((Lorentz.SL2C.toLorentzGroup Λ).1 a μ : ℝ) : ℂ) •
          ((1 : ℂ) ⊗ₜ[ℝ] ofA a φ) := by
  rw [complexRepLorentzGroup_tmul, repLorentzGroup_ofA, TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [TensorProduct.tmul_smul,
    show ((((Lorentz.SL2C.toLorentzGroup Λ).1 a μ : ℝ)) : ℂ)
      = algebraMap ℝ ℂ ((Lorentz.SL2C.toLorentzGroup Λ).1 a μ) from rfl,
    algebraMap_smul]

end GaugeJetAlgebra

end StandardModel
