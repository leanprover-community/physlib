/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.GlobalGaugeGroup.JetLieAlgebra
/-!
# The gauge jets of a global gauge group

The Taylor series at a point of the gauge transformations.

## i. Overview

A gauge transformation with global gauge group `G` is a smooth map from spacetime into `G`.
Its jet at the base point is an invertible matrix of jets `U` with value `U (0)` in `G`.
Since a map into `GL(κ, ℂ)` starting in `G` stays in `G` exactly when its Maurer–Cartan
form takes values in the Lie algebra, the gauge jets are the invertible matrices of jets
with value in `G` and Maurer–Cartan form `(∂_μ U) U⁻¹` a Lie algebra jet.

That the gauge jets form a group rests on conjugation `A ↦ U⁻¹ A U` preserving the Lie
algebra jets. Its derivative is `U⁻¹ (∂_μ A − [ω_μ, A]) U` with `ω_μ = (∂_μ U) U⁻¹`, again
of the same form, so every base-point derivative reduces to a value `g⁻¹ a g` with `g ∈ G`
and `a ∈ 𝔤`.

## ii. Key results

- `GlobalGaugeGroup.IsGaugeJet` : the condition for an invertible matrix of jets to be a
  gauge jet.
- `GlobalGaugeGroup.inv_mul_mul_mem_jetLieAlgebra` : conjugation by a gauge jet preserves
  the Lie algebra jets.
- `GlobalGaugeGroup.gaugeJetGroup` : the group of gauge jets.

## iii. Table of contents

- A. Gauge jets
- B. Conjugation of Lie algebra jets
- C. The group of gauge jets

## iv. References

* None.

-/

@[expose] public section

open Matrix MvPowerSeries SpaceTimeAlgebra

namespace GlobalGaugeGroup

variable {κ : Type} [Fintype κ] [DecidableEq κ] (G : GlobalGaugeGroup κ)

/-!

## A. Gauge jets

-/

/-- An invertible matrix of jets is a gauge jet when its value lies in the group and its
  Maurer–Cartan form `(∂_μ U) U⁻¹` is a Lie algebra jet. -/
def IsGaugeJet (U : GeneralLinearGroup κ SpaceTimeAlgebra) : Prop :=
  unitsEval U ∈ G.group ∧ ∀ μ, (U : Matrix κ κ SpaceTimeAlgebra).map (pderiv μ) *
    (↑U⁻¹ : Matrix κ κ SpaceTimeAlgebra) ∈ G.jetLieAlgebra

/-!

## B. Conjugation of Lie algebra jets

-/

/-- Conjugation `A ↦ U⁻¹ A U` by a gauge jet preserves the Lie algebra jets. At the base
  point it is the adjoint action of the group, and the derivative of `U⁻¹ A U` is again of
  this form, `U⁻¹ (∂_μ A − [ω_μ, A]) U`. -/
lemma inv_mul_mul_mem_jetLieAlgebra {U : GeneralLinearGroup κ SpaceTimeAlgebra}
    (hU : G.IsGaugeJet U) {A : Matrix κ κ SpaceTimeAlgebra} (hA : A ∈ G.jetLieAlgebra) :
    (↑U⁻¹ : Matrix κ κ SpaceTimeAlgebra) * A * U ∈ G.jetLieAlgebra := by
  refine G.mem_jetLieAlgebra_of
    (P := fun D => ∃ A ∈ G.jetLieAlgebra, D = (↑U⁻¹ : Matrix κ κ SpaceTimeAlgebra) * A * U)
    ?_ ?_ ⟨A, hA, rfl⟩
  · rintro _ ⟨A, hA, rfl⟩
    have h := conj_mem_lieAlgebraOfIsClosed (hH := G.isClosed)
      ⟨(unitsEval U)⁻¹, inv_mem hU.1⟩ (hA 0)
    rw [derivValueMatrix_zero] at h
    rw [map_mul, map_mul, ← unitsEval_val, ← unitsEval_val, map_inv]
    show _ ∈ lieAlgebraOfIsClosed G.group G.isClosed
    simpa using h
  · rintro _ ⟨A, hA, rfl⟩ μ
    exact ⟨_, sub_mem (G.map_pderiv_mem_jetLieAlgebra hA μ)
      (G.commutator_mem_jetLieAlgebra (hU.2 μ) hA),
      map_pderiv_conj_of_mul_eq_one μ U.mul_inv U.inv_mul A⟩

/-- The inverse of a gauge jet is a gauge jet: its Maurer–Cartan form is
  `−U⁻¹ ((∂_μ U) U⁻¹) U`. -/
lemma isGaugeJet_inv {U : GeneralLinearGroup κ SpaceTimeAlgebra} (hU : G.IsGaugeJet U) :
    G.IsGaugeJet U⁻¹ := by
  refine ⟨by rw [map_inv]; exact inv_mem hU.1, fun μ => ?_⟩
  rw [inv_inv, map_pderiv_of_mul_eq_one μ U.mul_inv U.inv_mul, neg_mul,
    mul_assoc (↑U⁻¹ : Matrix κ κ SpaceTimeAlgebra)]
  exact neg_mem (G.inv_mul_mul_mem_jetLieAlgebra hU (hU.2 μ))

/-- Conjugation `A ↦ U A U⁻¹` by a gauge jet preserves the Lie algebra jets. -/
lemma mul_mul_inv_mem_jetLieAlgebra {U : GeneralLinearGroup κ SpaceTimeAlgebra}
    (hU : G.IsGaugeJet U) {A : Matrix κ κ SpaceTimeAlgebra} (hA : A ∈ G.jetLieAlgebra) :
    (U : Matrix κ κ SpaceTimeAlgebra) * A * (↑U⁻¹ : Matrix κ κ SpaceTimeAlgebra)
      ∈ G.jetLieAlgebra := by
  have h := G.inv_mul_mul_mem_jetLieAlgebra (G.isGaugeJet_inv hU) hA
  rwa [inv_inv] at h

/-!

## C. The group of gauge jets

-/

/-- The product of gauge jets is a gauge jet, by the cocycle law of the Maurer–Cartan form. -/
lemma isGaugeJet_mul {U V : GeneralLinearGroup κ SpaceTimeAlgebra} (hU : G.IsGaugeJet U)
    (hV : G.IsGaugeJet V) : G.IsGaugeJet (U * V) := by
  refine ⟨by rw [map_mul]; exact mul_mem hU.1 hV.1, fun μ => ?_⟩
  rw [_root_.mul_inv_rev, Units.val_mul, Units.val_mul, map_pderiv_mul_mul_mul μ V.mul_inv]
  exact add_mem (hU.2 μ) (G.mul_mul_inv_mem_jetLieAlgebra hU (hV.2 μ))

/-- The jet of a constant gauge transformation is a gauge jet. -/
lemma isGaugeJet_unitsOfConstant {g : GeneralLinearGroup κ ℂ} (hg : g ∈ G.group) :
    G.IsGaugeJet (unitsOfConstant g) := by
  refine ⟨by rw [unitsEval_unitsOfConstant]; exact hg, fun μ => ?_⟩
  rw [unitsOfConstant_val, map_pderiv_mapMatrix_C, zero_mul]
  exact G.jetLieAlgebra.zero_mem

/-- The group of gauge jets: the invertible matrices of jets with value in the group and
  Maurer–Cartan form a Lie algebra jet. These are the Taylor series of smooth maps from
  spacetime into the group, the analogue of `JetSU` and `JetU1`, and not the jet group of
  diffeomorphisms of differential geometry. -/
def gaugeJetGroup : Subgroup (GeneralLinearGroup κ SpaceTimeAlgebra) where
  carrier := {U | G.IsGaugeJet U}
  one_mem' := by simpa using G.isGaugeJet_unitsOfConstant (one_mem G.group)
  mul_mem' hU hV := G.isGaugeJet_mul hU hV
  inv_mem' hU := G.isGaugeJet_inv hU

@[simp]
lemma mem_gaugeJetGroup {U : GeneralLinearGroup κ SpaceTimeAlgebra} :
    U ∈ G.gaugeJetGroup ↔ G.IsGaugeJet U := Iff.rfl

end GlobalGaugeGroup
