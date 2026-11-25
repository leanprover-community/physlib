/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.MatterField.FieldDerivSpace.Basic
public import Mathlib.Analysis.Normed.Operator.Prod
/-!
# The direct sum of two matter fields

Two matter fields of one mass weight and statistics as a single matter field.

## i. Overview

Two matter fields of a gauge theory with the same mass weight and the same declared
statistics combine into one, valued in the product of their value spaces. This is the
operation that lets a multiplet be described either as one field or as its summands: three
generations of a fermion type, or the two chiralities of a Dirac field, are the direct sum
of their pieces.

Every piece of data acts componentwise. The Lorentz representation and the infinitesimal
gauge action are `LinearMap.prodMap` of the two; the jet gauge action is the pair of the
two, read through the identification `jetProdEquiv` of the jets of a product with the
product of the jets. The direct sum is one `MatterField`, with one mass weight and one
statistic, so it takes as hypotheses that the two fields have the same mass weight and the
same statistics.

The gauge group acts through `repProd`, a continuous homomorphism into the units of the
continuous linear maps of the product. The infinitesimal and jet gauge actions of the direct
sum are derived from it, and what has to be proved is that they are the componentwise ones,
`prod_repAlgebra` and `prod_repJet`.

## ii. Key results

- `GlobalGaugeGroup.MatterField.repJetProd` : the jet gauge action of a direct sum.
- `GlobalGaugeGroup.MatterField.repAlgebraProd` : the infinitesimal gauge action of a direct
  sum.
- `GlobalGaugeGroup.MatterField.repCoeff_repJetProd` : its base-point Taylor coefficients are
  the pair of those of the summands.
- `GlobalGaugeGroup.MatterField.prod` : the direct sum of two matter fields of the same mass
  weight and statistics.
- `FieldDerivSpace.prodEquiv` : the component space of a direct sum splits.

## iii. Table of contents

- A. The direct sum of two matter fields
- B. The componentwise gauge actions
- C. The derived actions of the direct sum
- D. The component space of a direct sum

## iv. References

* None.

-/

@[expose] public section

open Matrix MatrixGroups TensorProduct

namespace GlobalGaugeGroup.MatterField

variable {κ : Type} [Fintype κ] [DecidableEq κ] {G : GlobalGaugeGroup κ}

/-!

## A. The direct sum of two matter fields

Two matter fields of the same mass weight and statistics combine into one, valued in the
product of their value spaces. The global gauge group and the Lorentz group act componentwise,
and the weight and statistics are those of the first summand.

-/

section Prod

variable (M N : G.MatterField)

/-- The pair of continuous linear maps `(f, g)` as the continuous linear map `f × g` of the
  product, a ring homomorphism. -/
noncomputable def prodMapRingHom :
    (M.V →L[ℂ] M.V) × (N.V →L[ℂ] N.V) →+* ((M.V × N.V) →L[ℂ] (M.V × N.V)) where
  toFun p := p.1.prodMap p.2
  map_one' := ContinuousLinearMap.ext fun _ => rfl
  map_mul' _ _ := ContinuousLinearMap.ext fun _ => rfl
  map_zero' := ContinuousLinearMap.ext fun _ => rfl
  map_add' _ _ := ContinuousLinearMap.ext fun _ => rfl

lemma continuous_prodMapRingHom : Continuous (prodMapRingHom M N) :=
  (ContinuousLinearMap.prodMapL ℂ M.V M.V N.V N.V).continuous

/-- The direct sum `g ↦ ρ_M(g) × ρ_N(g)` of the representations of two matter fields. -/
noncomputable def repProd : G.group →ₜ* ((M.V × N.V) →L[ℂ] (M.V × N.V))ˣ where
  toMonoidHom := (Units.map (prodMapRingHom M N).toMonoidHom).comp
    (MulEquiv.prodUnits.symm.toMonoidHom.comp (M.rep.toMonoidHom.prod N.rep.toMonoidHom))
  continuous_toFun := Units.continuous_iff.2
    ⟨(continuous_prodMapRingHom M N).comp ((Units.continuous_val.comp M.rep.continuous).prodMk
        (Units.continuous_val.comp N.rep.continuous)),
      (continuous_prodMapRingHom M N).comp ((Units.continuous_coe_inv.comp M.rep.continuous).prodMk
        (Units.continuous_coe_inv.comp N.rep.continuous))⟩

@[simp]
lemma repProd_apply (g : G.group) :
    ((repProd M N g : ((M.V × N.V) →L[ℂ] (M.V × N.V))ˣ) : (M.V × N.V) →L[ℂ] (M.V × N.V)) =
      ((M.rep g : (M.V →L[ℂ] M.V)ˣ) : M.V →L[ℂ] M.V).prodMap
        ((N.rep g : (N.V →L[ℂ] N.V)ˣ) : N.V →L[ℂ] N.V) := rfl

/-- The direct sum of two matter fields of the same mass weight and statistics, as one
  field valued in `M.V × N.V`, on which the global gauge group and the Lorentz group act
  componentwise, with the weight and statistics of `M`. -/
noncomputable def prod (_h : M.massWeight = N.massWeight) (_hσ : M.statistic = N.statistic) :
    G.MatterField where
  V := M.V × N.V
  rep := repProd M N
  repLorentz := M.repLorentz.prod N.repLorentz
  massWeight := M.massWeight
  statistic := M.statistic

variable (h : M.massWeight = N.massWeight) (hσ : M.statistic = N.statistic)

@[simp]
lemma prod_V : (prod M N h hσ).V = (M.V × N.V) := rfl

@[simp]
lemma prod_repLorentz : (prod M N h hσ).repLorentz = M.repLorentz.prod N.repLorentz := rfl

@[simp]
lemma prod_massWeight : (prod M N h hσ).massWeight = M.massWeight := rfl

@[simp]
lemma prod_statistic : (prod M N h hσ).statistic = M.statistic := rfl

/-!

## B. The componentwise gauge actions

Every other piece of data acts componentwise. The infinitesimal gauge action is
`LinearMap.prodMap` of the two, and the jet gauge action is read through the identification
`jetProdEquiv` of the jets of a product with the product of the jets. What has to be checked
is the last field, that the componentwise algebra action still generates the componentwise
jet action.

-/

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

/-- The jet gauge action of a direct sum, the two actions read through the
  identification of the jets of `M.V × N.V` with the pair of jets. -/
noncomputable def repJetProd :
    Representation ℂ G.gaugeJetGroup (SpaceTimeAlgebra ⊗[ℂ] (M.V × N.V)) where
  toFun U := LinearEquiv.conjRingEquiv jetProdEquiv.symm ((M.repJet.prod N.repJet) U)
  map_one' := by rw [map_one, map_one]
  map_mul' U W := by rw [map_mul, map_mul]

lemma repJetProd_apply (U : G.gaugeJetGroup) (z : SpaceTimeAlgebra ⊗[ℂ] (M.V × N.V)) :
    repJetProd M N U z =
      jetProdEquiv.symm (M.repJet U (jetProdEquiv z).1, N.repJet U (jetProdEquiv z).2) := rfl

/-- The infinitesimal action of a direct sum, the two actions on the two summands. -/
noncomputable def repAlgebraProd : G.lieSubalgebra →ₗ[ℝ] (M.V × N.V) →ₗ[ℂ] (M.V × N.V) where
  toFun c := (M.repAlgebra c).prodMap (N.repAlgebra c)
  map_add' c₁ c₂ := by rw [map_add, map_add, prodMap_add_prodMap]
  map_smul' r c := by
    rw [map_smul, map_smul, RingHom.id_apply]
    exact LinearMap.ext fun _ => rfl

@[simp]
lemma repAlgebraProd_apply (c : G.lieSubalgebra) :
    repAlgebraProd M N c = (M.repAlgebra c).prodMap (N.repAlgebra c) := rfl

/-- The base-point Taylor coefficients of the summed jet action are the pair of the
  coefficients of the summands, since `jetOfConstant`, `jetIteratedDeriv` and `jetEval` all act
  componentwise through `jetProdEquiv`. -/
lemma repCoeff_repJetProd (U : G.gaugeJetGroup) (x : Multiset (Fin 1 ⊕ Fin 3)) :
    GlobalGaugeGroup.repCoeff (repJetProd M N) U x =
      (GlobalGaugeGroup.repCoeff M.repJet U x).prodMap
        (GlobalGaugeGroup.repCoeff N.repJet U x) := by
  refine LinearMap.ext fun p => ?_
  show jetEval (jetIteratedDeriv x (repJetProd M N U (jetOfConstant p))) = _
  rw [jetEval_prod, jetProdEquiv_jetIteratedDeriv,
    show jetProdEquiv (repJetProd M N U (jetOfConstant p))
        = (M.repJet U (jetOfConstant p.1), N.repJet U (jetOfConstant p.2)) from by
      rw [repJetProd_apply, LinearEquiv.apply_symm_apply]
      rfl]
  rfl

/-- The componentwise jet action is fibrewise. -/
lemma repJetProd_smul (U : G.gaugeJetGroup) (χ : SpaceTimeAlgebra)
    (z : SpaceTimeAlgebra ⊗[ℂ] (M.V × N.V)) : repJetProd M N U (χ • z) = χ • repJetProd M N
      U z := by
  rw [repJetProd_apply, repJetProd_apply, jetProdEquiv_smul, M.repJet_smul, N.repJet_smul,
    jetProdEquiv_symm_smul]

/-- The componentwise algebra action generates the componentwise jet action. Both laws
  of `IsInfinitesimalActionOf` are the corresponding laws of the summands, read through
  `repCoeff_repJetProd`, since `prodMap` is additive in both slots at once and composes
  componentwise. -/
lemma isInfinitesimalActionOf_repAlgebraProd :
    G.IsInfinitesimalActionOf (repAlgebraProd M N) (repJetProd M N) where
  repCoeff_cons U μ x := by
    rw [repCoeff_repJetProd, M.isInfinitesimalActionOf.repCoeff_cons U μ x,
      N.isInfinitesimalActionOf.repCoeff_cons U μ x,
      show ∀ (f : M.V →ₗ[ℂ] M.V) (g : N.V →ₗ[ℂ] N.V),
          (-f).prodMap (-g) = -(f.prodMap g) from fun _ _ => LinearMap.ext fun _ => rfl,
      prodMap_multiset_sum]
    refine congrArg Neg.neg (congrArg Multiset.sum (Multiset.map_congr rfl fun p _ => ?_))
    rw [repCoeff_repJetProd, repAlgebraProd_apply, LinearMap.prodMap_comp]
  repCoeff_act U x c := by
    rw [repCoeff_repJetProd, repAlgebraProd_apply, LinearMap.prodMap_comp,
      M.isInfinitesimalActionOf.repCoeff_act U x c,
      N.isInfinitesimalActionOf.repCoeff_act U x c, prodMap_multiset_sum]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun p _ => ?_)
    rw [repCoeff_repJetProd, repAlgebraProd_apply, LinearMap.prodMap_comp]

/-!

## C. The derived actions of the direct sum

The Lie algebra action and the jet gauge action that the direct sum inherits from its
representation are the componentwise ones.

-/

/-- The Lie algebra acts on a direct sum componentwise, since the exponential of `dρ_M(X) × dρ_N(X)`
  is the pair of exponentials. -/
lemma lieAlgebraRep_prod (X : G.lieSubalgebra) :
    lieAlgebraRep (prod M N h hσ) X = (lieAlgebraRep M X).prodMap (lieAlgebraRep N X) := by
  let _ : NormedAlgebra ℚ (M.V →L[ℂ] M.V) := .restrictScalars ℚ ℝ _
  let _ : NormedAlgebra ℚ (N.V →L[ℂ] N.V) := .restrictScalars ℚ ℝ _
  let _ : NormedAlgebra ℚ ((M.V × N.V) →L[ℂ] (M.V × N.V)) := .restrictScalars ℚ ℝ _
  refine lieAlgebraRep_eq_of _ fun t g hg => ?_
  change prodMapRingHom M N (((M.rep g : (M.V →L[ℂ] M.V)ˣ) : M.V →L[ℂ] M.V),
    ((N.rep g : (N.V →L[ℂ] N.V)ˣ) : N.V →L[ℂ] N.V)) = _
  have hexp : (NormedSpace.exp (t • lieAlgebraRep M X), NormedSpace.exp (t • lieAlgebraRep N X)) =
      NormedSpace.exp (t • lieAlgebraRep M X, t • lieAlgebraRep N X) :=
    Prod.ext (by rw [Prod.fst_exp]) (by rw [Prod.snd_exp])
  rw [rep_eq_exp_lieAlgebraRep M hg, rep_eq_exp_lieAlgebraRep N hg, hexp,
    NormedSpace.map_exp (prodMapRingHom M N) (continuous_prodMapRingHom M N)]
  rfl

/-- The Lie algebra of a direct sum acts componentwise. -/
@[simp]
lemma prod_repAlgebra : (prod M N h hσ).repAlgebra = repAlgebraProd M N :=
  LinearMap.ext fun c => by
    rw [repAlgebra_apply, lieAlgebraRep_prod]
    rfl

/-- The gauge jets act on a direct sum componentwise, since both actions are generated by the
  componentwise action of the Lie algebra, and agree at the base point. -/
@[simp]
lemma prod_repJet : (prod M N h hσ).repJet = repJetProd M N := by
  have hI := (prod M N h hσ).isInfinitesimalActionOf
  rw [prod_repAlgebra] at hI
  refine hI.eq_of_repCoeff_zero (isInfinitesimalActionOf_repAlgebraProd M N)
    (prod M N h hσ).repJet_smul (repJetProd_smul M N) fun U => ?_
  refine Eq.trans ?_ (repCoeff_repJetProd M N U 0).symm
  rw [repCoeff_repJet, repCoeff_repJet, repCoeff_repJet, repCoeff_zero, repCoeff_zero,
    repCoeff_zero]
  rfl

end Prod

/-!

## D. The component space of a direct sum

-/

/-- The component space of a direct sum splits. The component functions of the direct
  sum `M.prod N h hσ` are those of `M` together with those of `N`, since the dual and the conjugate
  both distribute over the finite product, and the derivative label is untouched. Only the
  value spaces enter, so the hypotheses `h` and `hσ` are carried along and not used. -/
noncomputable def _root_.FieldDerivSpace.prodEquiv (M N : G.MatterField)
    (h : M.massWeight = N.massWeight) (hσ : M.statistic = N.statistic) :
    FieldDerivSpace (M.prod N h hσ) ≃ₗ[ℂ] FieldDerivSpace M × FieldDerivSpace N :=
  (LinearEquiv.prodCongr
      (TensorProduct.congr (LinearEquiv.refl ℂ SpaceTimeDerivAlgebraℂ)
        (Module.dualProdDualEquivDual ℂ M.V N.V).symm)
      (TensorProduct.congr (LinearEquiv.refl ℂ SpaceTimeDerivAlgebraℂ)
        (((ConjModule.prodEquiv (k := ℂ) (M := M.V) (N := N.V)).symm.dualMap).trans
          (Module.dualProdDualEquivDual ℂ (ConjModule M.V) (ConjModule N.V)).symm))).trans <|
    (LinearEquiv.prodCongr (TensorProduct.prodRight ℂ ℂ _ _ _)
        (TensorProduct.prodRight ℂ ℂ _ _ _)).trans
      (LinearEquiv.prodProdProdComm ℂ _ _ _ _)

end GlobalGaugeGroup.MatterField
