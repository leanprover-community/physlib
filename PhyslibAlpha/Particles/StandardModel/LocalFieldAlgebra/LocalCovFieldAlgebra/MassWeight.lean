/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.LocalFieldAlgebra.LocalCovFieldAlgebra.Sector
public import PhyslibAlpha.Particles.StandardModel.LocalFieldAlgebra.LocalCovFieldAlgebra.Towers
/-!
# The mass-weight grading of the covariant field algebra of the Standard Model

The generic mass-weight grading of a covariant field algebra, at the mass-weight polynomial of
the Standard Model.

## i. Overview

The mass-weight polynomial `LocalCovFieldAlgebra.massWeightPoly` of the Standard Model gives the
field-strength tower `∇_l F_μν` weight `4 + 2 |l|`, the Higgs towers weight `2 + 2 n` and the
fermion towers weight `3 + 2 n`. The Higgs has mass weight two and every fermion mass weight
three. So the polynomial is a mass-weight polynomial in the sense of
`GaugeFieldData.LocalCovFieldAlgebra.IsMassWeightPoly`, every species has positive mass weight,
and the mass weights have the parity of the statistics. The generic grading, its weight
components, its filtration and the generic sectors therefore apply to the covariant field
algebra of the Standard Model. This file records the three facts and names the weight pieces and
the filtration at this polynomial.

## ii. Key results

- `StandardModel.LocalCovFieldAlgebra.isMassWeightPoly` : the mass-weight polynomial of the
  Standard Model gives every covariant generator its mass weight.
- `StandardModel.LocalCovFieldAlgebra.hasPositiveMassWeights`,
  `StandardModel.LocalCovFieldAlgebra.hasMassWeightParity` : the species weights are positive,
  odd for the fermions and even for the Higgs.
- `StandardModel.LocalCovFieldAlgebra.massWeightSubmodule`,
  `StandardModel.LocalCovFieldAlgebra.massWeightSubmoduleLE` : the weight pieces and the
  filtration of the covariant field algebra of the Standard Model.

## iii. Table of contents

- A. The mass-weight polynomial of the Standard Model
- B. The weight pieces and the filtration
- C. Stability under the gauge and Lorentz groups

## iv. References

* None.

-/

@[expose] public section

namespace StandardModel

open MatrixGroups

namespace LocalCovFieldAlgebra

/-!

## A. The mass-weight polynomial of the Standard Model

-/

/-- The mass-weight polynomial of the Standard Model gives every covariant generator its mass
  weight, `4 + 2 |l|` for the field-strength tower, `2 + 2 n` for the Higgs towers and
  `3 + 2 n` for the fermion towers. -/
lemma isMassWeightPoly : GaugeFieldData.LocalCovFieldAlgebra.IsMassWeightPoly massWeightPoly :=
  GaugeFieldData.LocalCovFieldAlgebra.isMassWeightPoly_of massWeightPoly
    (fun l μ ν φ => massWeightPoly_eq_monomial
      (GaugeFieldData.massWeight_covDerivFieldStrength fieldData.massWeightPoly
        (GaugeFieldData.massWeightPoly_gaugeField (T := fieldData)) l μ ν φ))
    (fun i {_n} l φ => by
      rw [fieldData_fermion_massWeight]
      exact massWeightPoly_eq_monomial (GaugeFieldData.massWeight_covDerivFermion
        fieldData.massWeightPoly
        (GaugeFieldData.massWeightPoly_gaugeField (T := fieldData)) i 3
        (massWeightPoly_fieldData_fermionSymbol i) l φ))
    (fun i {_n} l φ => by
      rw [fieldData_fermion_massWeight]
      exact massWeightPoly_eq_monomial
        (GaugeFieldData.massWeight_covDerivConjFermion fieldData.massWeightPoly
          (GaugeFieldData.massWeightPoly_gaugeField (T := fieldData)) i 3
          (massWeightPoly_fieldData_conjFermionSymbol i) l φ))
    (fun j {_n} l φ => by
      rw [fieldData_boson_massWeight]
      exact massWeightPoly_eq_monomial (GaugeFieldData.massWeight_covDerivBoson
        fieldData.massWeightPoly
        (GaugeFieldData.massWeightPoly_gaugeField (T := fieldData)) j 2
        (massWeightPoly_fieldData_bosonSymbol j) l φ))
    (fun j {_n} l φ => by
      rw [fieldData_boson_massWeight]
      exact massWeightPoly_eq_monomial
        (GaugeFieldData.massWeight_covDerivConjBoson fieldData.massWeightPoly
          (GaugeFieldData.massWeightPoly_gaugeField (T := fieldData)) j 2
          (massWeightPoly_fieldData_conjBosonSymbol j) l φ))

/-- Every species of the Standard Model has positive mass weight. -/
lemma hasPositiveMassWeights : fieldData.HasPositiveMassWeights :=
  ⟨fun i => by rw [fieldData_fermion_massWeight]; norm_num,
    fun j => by rw [fieldData_boson_massWeight]; norm_num⟩

/-- The fermions of the Standard Model have odd mass weight and the Higgs even mass weight. -/
lemma hasMassWeightParity : fieldData.HasMassWeightParity :=
  ⟨fun i => by rw [fieldData_fermion_massWeight]; exact ⟨1, rfl⟩,
    fun j => by rw [fieldData_boson_massWeight]; exact ⟨1, rfl⟩⟩

/-!

## B. The weight pieces and the filtration

-/

/-- The elements of the covariant field algebra of the Standard Model of mass weight exactly
  `n`. -/
noncomputable abbrev massWeightSubmodule (n : ℕ) : Submodule ℂ fieldData.LocalCovFieldAlgebra :=
  GaugeFieldData.LocalCovFieldAlgebra.massWeightSubmodule massWeightPoly n

/-- The elements of the covariant field algebra of the Standard Model of mass weight at most
  `w`. A Lagrangian of mass dimension at most `w / 2` lies here. -/
noncomputable abbrev massWeightSubmoduleLE (w : ℕ) : Submodule ℂ fieldData.LocalCovFieldAlgebra :=
  GaugeFieldData.LocalCovFieldAlgebra.massWeightSubmoduleLE massWeightPoly w

/-- The weight-zero part of the covariant field algebra is the scalars, the constant term of mass
  dimension zero. -/
lemma massWeightSubmodule_zero : massWeightSubmodule 0 = 1 :=
  GaugeFieldData.LocalCovFieldAlgebra.massWeightSubmodule_zero isMassWeightPoly
    hasPositiveMassWeights

/-- The filtration as a join over a finite index type. -/
lemma massWeightSubmoduleLE_eq_iSup (w : ℕ) :
    massWeightSubmoduleLE w = ⨆ k : Fin (w + 1), massWeightSubmodule (k : ℕ) :=
  GaugeFieldData.LocalCovFieldAlgebra.massWeightSubmoduleLE_eq_iSup w

/-- The weight-`w` piece is the join of the weight-`w` pieces of the sectors. -/
lemma massWeightSubmodule_eq_iSup_sectorMassWeight (w : ℕ) :
    massWeightSubmodule w = ⨆ A, fieldData.sectorMassWeight A w :=
  GaugeFieldData.massWeightSubmodule_eq_iSup_sectorMassWeight isMassWeightPoly w

/-!

## C. Stability under the gauge and Lorentz groups

-/

/-- The global gauge group preserves the weight pieces. -/
lemma repGauge_mem_massWeightSubmodule {w : ℕ} {x : fieldData.LocalCovFieldAlgebra}
    (g : GaugeGroupI)
    (hx : x ∈ massWeightSubmodule w) : repGaugeGroupI g x ∈ massWeightSubmodule w :=
  GaugeFieldData.LocalCovFieldAlgebra.repValue_mem_massWeightSubmodule isMassWeightPoly
    (gaugeGroupEquiv g) hx

/-- The Lorentz group preserves the weight pieces. -/
lemma repLorentz_mem_massWeightSubmodule {w : ℕ} {x : fieldData.LocalCovFieldAlgebra} (Λ : SL(2,ℂ))
    (hx : x ∈ massWeightSubmodule w) : repLorentzGroup Λ x ∈ massWeightSubmodule w :=
  GaugeFieldData.LocalCovFieldAlgebra.repLorentzGroup_mem_massWeightSubmodule isMassWeightPoly
    fieldData_gaugeLorentzCompatible Λ hx

/-- The global gauge group preserves the weight pieces of every sector. -/
lemma repGauge_mem_sectorMassWeight {A : Finset GaugeFieldData.FieldKind} {w : ℕ}
    {x : fieldData.LocalCovFieldAlgebra} (g : GaugeGroupI)
    (hx : x ∈ fieldData.sectorMassWeight A w) :
    repGaugeGroupI g x ∈ fieldData.sectorMassWeight A w :=
  GaugeFieldData.repValue_mem_sectorMassWeight (gaugeGroupEquiv g) hx

/-- The Lorentz group preserves the weight pieces of every sector. -/
lemma repLorentz_mem_sectorMassWeight {A : Finset GaugeFieldData.FieldKind} {w : ℕ}
    {x : fieldData.LocalCovFieldAlgebra} (Λ : SL(2,ℂ)) (hx : x ∈ fieldData.sectorMassWeight A w) :
    repLorentzGroup Λ x ∈ fieldData.sectorMassWeight A w :=
  GaugeFieldData.repLorentzGroup_mem_sectorMassWeight fieldData_gaugeLorentzCompatible Λ hx

end LocalCovFieldAlgebra

end StandardModel
