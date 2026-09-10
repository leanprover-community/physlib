/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.ClassicalFieldTheory.GaugeTheory.MatterField.Basic
/-!
# The direct sum of two matter fields

## i. Overview

Two matter fields of a gauge theory with the same mass weight combine into one, valued in
the product of their value spaces. This is the operation that lets a multiplet be
described either as one field or as its summands: three generations of a fermion type, or
the two chiralities of a Dirac field, are the direct sum of their pieces.

Every piece of data acts componentwise. The Lorentz representation and the infinitesimal
gauge action are `LinearMap.prodMap` of the two; the jet gauge action is the pair of the
two, read through the identification `jetProdEquiv` of the jets of a product with the
product of the jets. The mass weight has to be shared: a `MatterField` carries a single
weight, so the direct sum takes the equality of the two as a hypothesis.

What has to be proved is the last field of the structure — that the componentwise
infinitesimal action still generates the componentwise jet action.

## ii. Key results

- `MatterField.repJetProd` : the jet gauge action of a direct sum.
- `MatterField.repAlgebraProd` : the infinitesimal gauge action of a direct sum.
- `MatterField.repCoeff_repJetProd` : its base-point Taylor coefficients are the pair of
  those of the summands.
- `MatterField.prod` : the direct sum of two matter fields of the same mass weight.

## iii. Table of contents

- A. The direct sum of two matter fields

-/

@[expose] public section

open Matrix MatrixGroups TensorProduct

namespace MatterField

variable {G : Type} [Group G] {𝔤 : Type} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
  {G₀ : Type} [Group G₀] {𝔤J : Type} [LieRing 𝔤J] [LieAlgebra ℝ 𝔤J]
  {jets : LocalGaugeData G 𝔤 G₀ 𝔤J}

/-!

## A. The direct sum of two matter fields

Two matter fields of the same mass weight combine into one, valued in the product of their
value spaces. Every piece of data acts componentwise: the Lorentz and gauge algebra
actions by `LinearMap.prodMap`, and the jet gauge action through the identification
`jetProdEquiv` of the jets of a product with the product of the jets. What has to be
checked is the last field — that the componentwise algebra action still generates the
componentwise jet action.

-/

section Prod

variable (M N : MatterField jets)

private lemma prodMap_add_prodMap {V₁ V₂ : Type} [AddCommGroup V₁] [Module ℂ V₁]
    [AddCommGroup V₂] [Module ℂ V₂] (f₁ f₂ : V₁ →ₗ[ℂ] V₁) (g₁ g₂ : V₂ →ₗ[ℂ] V₂) :
    (f₁ + f₂).prodMap (g₁ + g₂) = f₁.prodMap g₁ + f₂.prodMap g₂ :=
  LinearMap.ext fun _ => rfl

private lemma prodMap_multiset_sum {ι V₁ V₂ : Type} [AddCommGroup V₁] [Module ℂ V₁]
    [AddCommGroup V₂] [Module ℂ V₂] (S : Multiset ι) (f : ι → V₁ →ₗ[ℂ] V₁)
    (g : ι → V₂ →ₗ[ℂ] V₂) :
    ((S.map f).sum).prodMap ((S.map g).sum) = (S.map fun i => (f i).prodMap (g i)).sum := by
  induction S using Multiset.induction_on with
  | empty => exact LinearMap.ext fun _ => rfl
  | cons i S ih =>
      rw [Multiset.map_cons, Multiset.map_cons, Multiset.map_cons, Multiset.sum_cons,
        Multiset.sum_cons, Multiset.sum_cons, prodMap_add_prodMap, ih]

/-- **The jet gauge action of a direct sum**: the two actions, read through the
  identification of the jets of `M.V × N.V` with the pair of jets. -/
noncomputable def repJetProd :
    Representation ℂ G (JetRing ⊗[ℂ] (M.V × N.V)) where
  toFun U := LinearEquiv.conjRingEquiv jetProdEquiv.symm ((M.repJet.prod N.repJet) U)
  map_one' := by rw [map_one, map_one]
  map_mul' U W := by rw [map_mul, map_mul]

lemma repJetProd_apply (U : G) (z : JetRing ⊗[ℂ] (M.V × N.V)) :
    repJetProd M N U z =
      jetProdEquiv.symm (M.repJet U (jetProdEquiv z).1, N.repJet U (jetProdEquiv z).2) := rfl

/-- **The infinitesimal action of a direct sum**: the two actions on the two summands. -/
noncomputable def repAlgebraProd : 𝔤 →ₗ[ℝ] (M.V × N.V) →ₗ[ℂ] (M.V × N.V) where
  toFun c := (M.repAlgebra c).prodMap (N.repAlgebra c)
  map_add' c₁ c₂ := by rw [map_add, map_add, prodMap_add_prodMap]
  map_smul' r c := by
    rw [map_smul, map_smul, RingHom.id_apply]
    exact LinearMap.ext fun _ => rfl

@[simp]
lemma repAlgebraProd_apply (c : 𝔤) :
    repAlgebraProd M N c = (M.repAlgebra c).prodMap (N.repAlgebra c) := rfl

/-- The base-point Taylor coefficients of the summed jet action are the pair of the
  coefficients of the summands: `jetOfConstant`, `jetIteratedDeriv` and `jetEval` all act
  componentwise through `jetProdEquiv`. -/
lemma repCoeff_repJetProd (U : G) (x : Multiset (Fin 1 ⊕ Fin 3)) :
    GaugeAlgebraRealization.repCoeff (repJetProd M N) U x =
      (GaugeAlgebraRealization.repCoeff M.repJet U x).prodMap
        (GaugeAlgebraRealization.repCoeff N.repJet U x) := by
  refine LinearMap.ext fun p => ?_
  show jetEval (jetIteratedDeriv x (repJetProd M N U (jetOfConstant p))) = _
  rw [jetEval_prod, jetProdEquiv_jetIteratedDeriv,
    show jetProdEquiv (repJetProd M N U (jetOfConstant p))
        = (M.repJet U (jetOfConstant p.1), N.repJet U (jetOfConstant p.2)) from by
      rw [repJetProd_apply, LinearEquiv.apply_symm_apply]
      rfl]
  rfl

/-- **The componentwise algebra action generates the componentwise jet action**: both laws
  of `IsInfinitesimalActionOf` are the corresponding laws of the summands, read through
  `repCoeff_repJetProd`, since `prodMap` is additive in both slots at once and composes
  componentwise. -/
lemma isInfinitesimalActionOf_repAlgebraProd :
    jets.IsInfinitesimalActionOf (repAlgebraProd M N) (repJetProd M N) where
  repCoeff_cons U μ x := by
    rw [repCoeff_repJetProd, M.repAlgebra_isInfinitesimalAction.repCoeff_cons U μ x,
      N.repAlgebra_isInfinitesimalAction.repCoeff_cons U μ x,
      show ∀ (f : M.V →ₗ[ℂ] M.V) (g : N.V →ₗ[ℂ] N.V),
          (-f).prodMap (-g) = -(f.prodMap g) from fun _ _ => LinearMap.ext fun _ => rfl,
      prodMap_multiset_sum]
    refine congrArg Neg.neg (congrArg Multiset.sum (Multiset.map_congr rfl fun p _ => ?_))
    rw [repCoeff_repJetProd, repAlgebraProd_apply, LinearMap.prodMap_comp]
  repCoeff_act U x c := by
    rw [repCoeff_repJetProd, repAlgebraProd_apply, LinearMap.prodMap_comp,
      M.repAlgebra_isInfinitesimalAction.repCoeff_act U x c,
      N.repAlgebra_isInfinitesimalAction.repCoeff_act U x c, prodMap_multiset_sum]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun p _ => ?_)
    rw [repCoeff_repJetProd, repAlgebraProd_apply, LinearMap.prodMap_comp]

/-- **The direct sum of two matter fields** of the same mass weight: one field valued in
  `M.V × N.V`, with every action acting componentwise. Fields of different mass weight do
  not sum — a `MatterField` carries one weight, which is what makes the mass-weight
  grading of its field algebra well defined. -/
noncomputable def prod (_h : M.massWeight = N.massWeight) : MatterField jets where
  V := M.V × N.V
  repLorentz := M.repLorentz.prod N.repLorentz
  repJet := repJetProd M N
  repAlgebra := repAlgebraProd M N
  repJet_smul U χ z := by
    rw [repJetProd_apply, repJetProd_apply, jetProdEquiv_smul, M.repJet_smul, N.repJet_smul,
      jetProdEquiv_symm_smul]
  repAlgebra_isInfinitesimalAction := isInfinitesimalActionOf_repAlgebraProd M N
  massWeight := M.massWeight

@[simp]
lemma prod_V (h : M.massWeight = N.massWeight) : (prod M N h).V = (M.V × N.V) := rfl

@[simp]
lemma prod_repJet (h : M.massWeight = N.massWeight) :
    (prod M N h).repJet = repJetProd M N := rfl

@[simp]
lemma prod_repAlgebra (h : M.massWeight = N.massWeight) :
    (prod M N h).repAlgebra = repAlgebraProd M N := rfl

@[simp]
lemma prod_repLorentz (h : M.massWeight = N.massWeight) :
    (prod M N h).repLorentz = M.repLorentz.prod N.repLorentz := rfl

@[simp]
lemma prod_massWeight (h : M.massWeight = N.massWeight) :
    (prod M N h).massWeight = M.massWeight := rfl

/-- The shared weight, read off the second summand: this is what the hypothesis of `prod`
  buys — the direct sum has one weight, and it is the weight of either summand. -/
lemma prod_massWeight_right (h : M.massWeight = N.massWeight) :
    (prod M N h).massWeight = N.massWeight := h

end Prod

end MatterField
