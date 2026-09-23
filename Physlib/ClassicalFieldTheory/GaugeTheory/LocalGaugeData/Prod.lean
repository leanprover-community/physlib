/-
Copyright (c) 2026 Jinzheng Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li
-/
module

public import Physlib.ClassicalFieldTheory.GaugeTheory.MatterField.MatrixRep.Factors
public import Mathlib.Algebra.Lie.Prod
/-!
# The product of local gauge data

## i. Overview

The local gauge data of a product of gauge groups: every structure map acts
componentwise, and every law holds componentwise. A `U(1)` or `SU(n)` factor of either
side lifts to a factor of the product, and the product of two faithful packages is
faithful.

## ii. Key results

- `LocalGaugeData.prod` : the product of two local gauge data.
- `U1Factor.inl`, `U1Factor.inr`, `SUFactor.inl`, `SUFactor.inr` : lifting factors to
  the product.
- `LocalGaugeData.instFaithfulProd` : the product of faithful packages is faithful.

## iii. Table of contents

- A. Componentwise representations
- B. The product
- C. Lifting factors
- D. Faithfulness

-/

@[expose] public section

/-!

## A. Componentwise representations

-/

/-- The componentwise representation of a product group on a product space. -/
noncomputable def Representation.prodMap {k G₁ G₂ V₁ V₂ : Type*} [CommSemiring k]
    [Monoid G₁] [Monoid G₂] [AddCommMonoid V₁] [Module k V₁] [AddCommMonoid V₂] [Module k V₂]
    (ρ₁ : Representation k G₁ V₁) (ρ₂ : Representation k G₂ V₂) :
    Representation k (G₁ × G₂) (V₁ × V₂) where
  toFun p := (ρ₁ p.1).prodMap (ρ₂ p.2)
  map_one' := by
    refine LinearMap.ext fun v => ?_
    simp
  map_mul' p q := by
    refine LinearMap.ext fun v => ?_
    simp [Module.End.mul_apply]

@[simp]
lemma Representation.prodMap_apply {k G₁ G₂ V₁ V₂ : Type*} [CommSemiring k]
    [Monoid G₁] [Monoid G₂] [AddCommMonoid V₁] [Module k V₁] [AddCommMonoid V₂] [Module k V₂]
    (ρ₁ : Representation k G₁ V₁) (ρ₂ : Representation k G₂ V₂) (p : G₁ × G₂) (v : V₁ × V₂) :
    Representation.prodMap ρ₁ ρ₂ p v = (ρ₁ p.1 v.1, ρ₂ p.2 v.2) := rfl

namespace LocalGaugeData

variable {G₁ : Type} [Group G₁] {𝔤₁ : Type} [LieRing 𝔤₁] [LieAlgebra ℝ 𝔤₁]
  {G₀₁ : Type} [Group G₀₁] {𝔤J₁ : Type} [LieRing 𝔤J₁] [LieAlgebra ℝ 𝔤J₁]
  {G₂ : Type} [Group G₂] {𝔤₂ : Type} [LieRing 𝔤₂] [LieAlgebra ℝ 𝔤₂]
  {G₀₂ : Type} [Group G₀₂] {𝔤J₂ : Type} [LieRing 𝔤J₂] [LieAlgebra ℝ 𝔤J₂]
  (j₁ : LocalGaugeData G₀₁ 𝔤₁ G₁ 𝔤J₁) (j₂ : LocalGaugeData G₀₂ 𝔤₂ G₂ 𝔤J₂)

/-!

## B. The product

-/

/-- **The product of two local gauge data**: every structure map acts componentwise. -/
noncomputable def prod : LocalGaugeData (G₀₁ × G₀₂) (𝔤₁ × 𝔤₂) (G₁ × G₂) (𝔤J₁ × 𝔤J₂) where
  eval := j₁.eval.prodMap j₂.eval
  ofConstant := j₁.ofConstant.prodMap j₂.ofConstant
  eval_ofConstant g := Prod.ext (j₁.eval_ofConstant g.1) (j₂.eval_ofConstant g.2)
  evalLie := j₁.evalLie.prodMap j₂.evalLie
  ofConstantLie := j₁.ofConstantLie.prodMap j₂.ofConstantLie
  ofConstantLie_lie a b := Prod.ext (j₁.ofConstantLie_lie a.1 b.1) (j₂.ofConstantLie_lie a.2 b.2)
  evalLie_ofConstantLie a :=
    Prod.ext (j₁.evalLie_ofConstantLie a.1) (j₂.evalLie_ofConstantLie a.2)
  deriv μ := (j₁.deriv μ).prodMap (j₂.deriv μ)
  deriv_comm μ ν a := Prod.ext (j₁.deriv_comm μ ν a.1) (j₂.deriv_comm μ ν a.2)
  deriv_bracket μ x y := Prod.ext (j₁.deriv_bracket μ x.1 y.1) (j₂.deriv_bracket μ x.2 y.2)
  deriv_ofConstantLie μ a :=
    Prod.ext (j₁.deriv_ofConstantLie μ a.1) (j₂.deriv_ofConstantLie μ a.2)
  coord μ := (j₁.coord μ).prodMap (j₂.coord μ)
  deriv_coord μ ν a := by
    by_cases h : μ = ν
    · subst h
      rw [ite_eq_left rfl]
      refine Prod.ext ?_ ?_
      · have := j₁.deriv_coord μ μ a.1
        rw [ite_eq_left rfl] at this
        exact this
      · have := j₂.deriv_coord μ μ a.2
        rw [ite_eq_left rfl] at this
        exact this
    · rw [ite_eq_right h, add_zero]
      refine Prod.ext ?_ ?_
      · have := j₁.deriv_coord μ ν a.1
        rw [ite_eq_right h, add_zero] at this
        exact this
      · have := j₂.deriv_coord μ ν a.2
        rw [ite_eq_right h, add_zero] at this
        exact this
  evalLie_coord μ a := Prod.ext (j₁.evalLie_coord μ a.1) (j₂.evalLie_coord μ a.2)
  coord_lie μ a b := Prod.ext (j₁.coord_lie μ a.1 b.1) (j₂.coord_lie μ a.2 b.2)
  adjoint := Representation.prodMap j₁.adjoint j₂.adjoint
  adjoint_lie U x y := Prod.ext (j₁.adjoint_lie U.1 x.1 y.1) (j₂.adjoint_lie U.2 x.2 y.2)
  adjointValue := Representation.prodMap j₁.adjointValue j₂.adjointValue
  evalLie_adjoint U x := Prod.ext (j₁.evalLie_adjoint U.1 x.1) (j₂.evalLie_adjoint U.2 x.2)
  maurerCartan U μ := (j₁.maurerCartan U.1 μ, j₂.maurerCartan U.2 μ)
  maurerCartan_ofConstant g μ :=
    Prod.ext (j₁.maurerCartan_ofConstant g.1 μ) (j₂.maurerCartan_ofConstant g.2 μ)
  maurerCartan_cocycle U V μ :=
    Prod.ext (j₁.maurerCartan_cocycle U.1 V.1 μ) (j₂.maurerCartan_cocycle U.2 V.2 μ)
  maurerCartan_structure U μ ν :=
    Prod.ext (j₁.maurerCartan_structure U.1 μ ν) (j₂.maurerCartan_structure U.2 μ ν)
  deriv_adjoint U μ x := Prod.ext (j₁.deriv_adjoint U.1 μ x.1) (j₂.deriv_adjoint U.2 μ x.2)

@[simp]
lemma prod_eval (U : G₁ × G₂) : (j₁.prod j₂).eval U = (j₁.eval U.1, j₂.eval U.2) := rfl

@[simp]
lemma prod_ofConstant (g : G₀₁ × G₀₂) :
    (j₁.prod j₂).ofConstant g = (j₁.ofConstant g.1, j₂.ofConstant g.2) := rfl

@[simp]
lemma prod_evalLie (a : 𝔤J₁ × 𝔤J₂) : (j₁.prod j₂).evalLie a = (j₁.evalLie a.1, j₂.evalLie a.2) :=
  rfl

@[simp]
lemma prod_ofConstantLie (a : 𝔤₁ × 𝔤₂) :
    (j₁.prod j₂).ofConstantLie a = (j₁.ofConstantLie a.1, j₂.ofConstantLie a.2) := rfl

@[simp]
lemma prod_deriv (μ : Fin 1 ⊕ Fin 3) (a : 𝔤J₁ × 𝔤J₂) :
    (j₁.prod j₂).deriv μ a = (j₁.deriv μ a.1, j₂.deriv μ a.2) := rfl

@[simp]
lemma prod_adjoint (U : G₁ × G₂) (a : 𝔤J₁ × 𝔤J₂) :
    (j₁.prod j₂).adjoint U a = (j₁.adjoint U.1 a.1, j₂.adjoint U.2 a.2) := rfl

@[simp]
lemma prod_maurerCartan (U : G₁ × G₂) (μ : Fin 1 ⊕ Fin 3) :
    (j₁.prod j₂).maurerCartan U μ = (j₁.maurerCartan U.1 μ, j₂.maurerCartan U.2 μ) := rfl

@[simp]
lemma prod_iteratedDeriv (s : Multiset (Fin 1 ⊕ Fin 3)) (a : 𝔤J₁ × 𝔤J₂) :
    (j₁.prod j₂).iteratedDeriv s a = (j₁.iteratedDeriv s a.1, j₂.iteratedDeriv s a.2) := by
  induction s using Multiset.induction_on generalizing a with
  | empty => simp
  | cons μ t ih =>
    rw [iteratedDeriv_cons, iteratedDeriv_cons, iteratedDeriv_cons, LinearMap.comp_apply,
      LinearMap.comp_apply, LinearMap.comp_apply, ih, prod_deriv]

/-!

## C. Lifting factors

-/

variable {j₁ j₂}

/-- A `U(1)` factor of the first gauge data, as a factor of the product. -/
noncomputable def _root_.LocalGaugeData.U1Factor.inl (F : U1Factor j₁) : U1Factor (j₁.prod j₂)
    where
  u := F.u.comp (MonoidHom.fst G₁ G₂)
  φ := F.φ.comp (LinearMap.fst ℝ 𝔤₁ 𝔤₂)
  φJ a := F.φJ a.1
  φJ_ofConstantLie c := F.φJ_ofConstantLie c.1
  φJ_cc_foldl p a := by
    rw [prod_iteratedDeriv]
    exact F.φJ_cc_foldl p a.1
  φJ_maurerCartan U μ := F.φJ_maurerCartan U.1 μ
  φJ_adjoint U c := F.φJ_adjoint U.1 c.1

/-- A `U(1)` factor of the second gauge data, as a factor of the product. -/
noncomputable def _root_.LocalGaugeData.U1Factor.inr (F : U1Factor j₂) : U1Factor (j₁.prod j₂)
    where
  u := F.u.comp (MonoidHom.snd G₁ G₂)
  φ := F.φ.comp (LinearMap.snd ℝ 𝔤₁ 𝔤₂)
  φJ a := F.φJ a.2
  φJ_ofConstantLie c := F.φJ_ofConstantLie c.2
  φJ_cc_foldl p a := by
    rw [prod_iteratedDeriv]
    exact F.φJ_cc_foldl p a.2
  φJ_maurerCartan U μ := F.φJ_maurerCartan U.2 μ
  φJ_adjoint U c := F.φJ_adjoint U.2 c.2

variable {n : Type} [Fintype n] [DecidableEq n]

/-- An `SU(n)` factor of the first gauge data, as a factor of the product. -/
noncomputable def _root_.LocalGaugeData.SUFactor.inl (F : SUFactor j₁ n) :
    SUFactor (j₁.prod j₂) n where
  u U := F.u U.1
  u_one := F.u_one
  u_mul U V := F.u_mul U.1 V.1
  u_unitary U := F.u_unitary U.1
  φ := F.φ.comp (LinearMap.fst ℝ 𝔤₁ 𝔤₂)
  φJ a := F.φJ a.1
  φJ_ofConstantLie c := F.φJ_ofConstantLie c.1
  φJ_cc_foldl p a := by
    rw [prod_iteratedDeriv]
    exact F.φJ_cc_foldl p a.1
  φJ_maurerCartan U μ := F.φJ_maurerCartan U.1 μ
  φJ_adjoint U c := F.φJ_adjoint U.1 c.1

/-- An `SU(n)` factor of the second gauge data, as a factor of the product. -/
noncomputable def _root_.LocalGaugeData.SUFactor.inr (F : SUFactor j₂ n) :
    SUFactor (j₁.prod j₂) n where
  u U := F.u U.2
  u_one := F.u_one
  u_mul U V := F.u_mul U.2 V.2
  u_unitary U := F.u_unitary U.2
  φ := F.φ.comp (LinearMap.snd ℝ 𝔤₁ 𝔤₂)
  φJ a := F.φJ a.2
  φJ_ofConstantLie c := F.φJ_ofConstantLie c.2
  φJ_cc_foldl p a := by
    rw [prod_iteratedDeriv]
    exact F.φJ_cc_foldl p a.2
  φJ_maurerCartan U μ := F.φJ_maurerCartan U.2 μ
  φJ_adjoint U c := F.φJ_adjoint U.2 c.2

/-!

## D. Faithfulness

-/

/-- The product of two faithful packages is faithful. -/
instance instFaithfulProd [j₁.Faithful] [j₂.Faithful] : (j₁.prod j₂).Faithful where
  ext_of_evalLie_iteratedDeriv {x y} h := by
    refine Prod.ext (j₁.ext_of_evalLie_iteratedDeriv fun s => ?_)
      (j₂.ext_of_evalLie_iteratedDeriv fun s => ?_)
    · have := congrArg Prod.fst (h s)
      simpa only [prod_evalLie, prod_iteratedDeriv] using this
    · have := congrArg Prod.snd (h s)
      simpa only [prod_evalLie, prod_iteratedDeriv] using this
  eq_ofConstant_of_maurerCartan_eq_zero {U} h := by
    refine Prod.ext ?_ ?_
    · exact Faithful.eq_ofConstant_of_maurerCartan_eq_zero (jets := j₁)
        (funext fun μ => congrArg Prod.fst (congrFun h μ))
    · exact Faithful.eq_ofConstant_of_maurerCartan_eq_zero (jets := j₂)
        (funext fun μ => congrArg Prod.snd (congrFun h μ))

end LocalGaugeData
