/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.GlobalGaugeGroup.LieAlgebra.Jet
/-!
# The jet gauge group of a global gauge group

The Taylor series at a point of the gauge transformations.

## i. Overview

A gauge transformation with global gauge group `G` is a smooth map from spacetime into `G`.
Its jet at the base point is an invertible matrix of jets `U` with value `U (0)` in `G`.
A map into `GL(κ, ℂ)` starting in `G` stays in `G` exactly when `(∂_μ U) U⁻¹` takes values
in the Lie algebra. The jet gauge group is therefore made of the invertible matrices of jets
with value in `G` and `(∂_μ U) U⁻¹` a Lie algebra jet. On the jet gauge group this is the
Maurer–Cartan form, of
`PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.GlobalGaugeGroup.MaurerCartan`.

That these form a group rests on conjugation by `U` preserving the Lie algebra jets, from
`PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.GlobalGaugeGroup.LieAlgebra.Jet`,
together with the Leibniz rule for `(∂_μ (U V)) (U V)⁻¹` and `(∂_μ U⁻¹) U`. Evaluation at
the base point is a homomorphism onto `G`, split by the constant gauge transformations.

## ii. Key results

- `GlobalGaugeGroup.gaugeJetGroup` : the jet gauge group.
- `GlobalGaugeGroup.evalGaugeJet` : evaluation of a gauge jet at the base point.
- `GlobalGaugeGroup.gaugeJetOfConstant` : the jet of a constant gauge transformation.
- `GlobalGaugeGroup.adjoint_mem_jetLieAlgebra` : the jet gauge group acts by conjugation on
  the Lie algebra jets.

## iii. Table of contents

- A. The jet gauge group
- B. Evaluation and constant gauge jets
- C. The adjoint action on the Lie algebra jets

## iv. References

* None.

-/

@[expose] public section

open Matrix MvPowerSeries SpaceTimeAlgebra

namespace GlobalGaugeGroup

variable {κ : Type} [Fintype κ] [DecidableEq κ] (G : GlobalGaugeGroup κ)

/-!

## A. The jet gauge group

-/

/-- The jet gauge group, the invertible matrices of jets `U` with value in the group and
  `(∂_μ U) U⁻¹` a Lie algebra jet. These are the Taylor series at a point of smooth maps from
  spacetime into the group, the gauge transformations seen to all orders. This is not the jet
  group of diffeomorphisms of differential geometry. -/
def gaugeJetGroup : Subgroup (GeneralLinearGroup κ SpaceTimeAlgebra) where
  carrier := {U | unitsEval U ∈ G.group ∧ ∀ μ, (U : Matrix κ κ SpaceTimeAlgebra).map (pderiv μ) *
    (↑U⁻¹ : Matrix κ κ SpaceTimeAlgebra) ∈ G.jetLieAlgebra}
  one_mem' := ⟨by rw [map_one]; exact one_mem _, fun μ => by
    rw [inv_one, Units.val_one, mul_one, ← map_one (C : ℂ →+* SpaceTimeAlgebra).mapMatrix,
      map_pderiv_mapMatrix_C]
    exact zero_mem _⟩
  mul_mem' {U V} hU hV := ⟨by rw [map_mul]; exact mul_mem hU.1 hV.1, fun μ => by
    rw [_root_.mul_inv_rev, Units.val_mul, Units.val_mul, map_pderiv_mul_mul_mul μ V.mul_inv]
    exact add_mem (hU.2 μ) (G.mul_mul_inv_mem_jetLieAlgebra hU.1 hU.2 (hV.2 μ))⟩
  inv_mem' {U} hU := ⟨by rw [map_inv]; exact inv_mem hU.1, fun μ => by
    rw [inv_inv]
    exact G.map_pderiv_inv_mul_mem_jetLieAlgebra hU.1 hU.2 μ⟩

lemma mem_gaugeJetGroup {U : GeneralLinearGroup κ SpaceTimeAlgebra} :
    U ∈ G.gaugeJetGroup ↔ unitsEval U ∈ G.group ∧ ∀ μ,
      (U : Matrix κ κ SpaceTimeAlgebra).map (pderiv μ) * (↑U⁻¹ : Matrix κ κ SpaceTimeAlgebra)
        ∈ G.jetLieAlgebra :=
  Iff.rfl

/-!

## B. Evaluation and constant gauge jets

-/

/-- The value of a gauge jet at the base point, as a homomorphism to the group. -/
noncomputable def evalGaugeJet : G.gaugeJetGroup →* G.group where
  toFun U := ⟨unitsEval U.1, U.2.1⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)

@[simp]
lemma evalGaugeJet_val (U : G.gaugeJetGroup) :
    ((G.evalGaugeJet U).1 : Matrix κ κ ℂ) =
      (constantCoeff : SpaceTimeAlgebra →+* ℂ).mapMatrix U.1 := rfl

/-- The jet of a constant gauge transformation is a gauge jet. -/
lemma unitsOfConstant_mem_gaugeJetGroup {g : GeneralLinearGroup κ ℂ} (hg : g ∈ G.group) :
    unitsOfConstant g ∈ G.gaugeJetGroup := by
  refine ⟨by rw [unitsEval_unitsOfConstant]; exact hg, fun μ => ?_⟩
  rw [unitsOfConstant_val, map_pderiv_mapMatrix_C, zero_mul]
  exact zero_mem _

/-- The jet of a constant gauge transformation, as a homomorphism from the group. -/
noncomputable def gaugeJetOfConstant : G.group →* G.gaugeJetGroup where
  toFun g := ⟨unitsOfConstant g.1, G.unitsOfConstant_mem_gaugeJetGroup g.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)

@[simp]
lemma gaugeJetOfConstant_val (g : G.group) :
    ((G.gaugeJetOfConstant g).1 : Matrix κ κ SpaceTimeAlgebra) =
      (C : ℂ →+* SpaceTimeAlgebra).mapMatrix g.1 := rfl

/-- A constant gauge jet has the constant as its value. -/
@[simp]
lemma evalGaugeJet_gaugeJetOfConstant (g : G.group) :
    G.evalGaugeJet (G.gaugeJetOfConstant g) = g :=
  Subtype.ext (unitsEval_unitsOfConstant g.1)

/-!

## C. The adjoint action on the Lie algebra jets

-/

/-- Conjugation `A ↦ U A U⁻¹` by a gauge jet preserves the Lie algebra jets. -/
lemma adjoint_mem_jetLieAlgebra (U : G.gaugeJetGroup) {A : Matrix κ κ SpaceTimeAlgebra}
    (hA : A ∈ G.jetLieAlgebra) :
    (U.1 : Matrix κ κ SpaceTimeAlgebra) * A * (↑U.1⁻¹ : Matrix κ κ SpaceTimeAlgebra)
      ∈ G.jetLieAlgebra :=
  G.mul_mul_inv_mem_jetLieAlgebra U.2.1 U.2.2 hA

/-- The group structure of the gauge jets, recorded directly so that instance search does not
  pass through the units of the matrices of jets. -/
noncomputable instance : Group G.gaugeJetGroup := inferInstance

end GlobalGaugeGroup
