/-
Copyright (c) 2026 Jinzheng Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li
-/
module

public import Physlib.Particles.StandardModel.Basic
public import Physlib.ClassicalFieldTheory.GaugeTheory.LocalFieldAlgebra.MassWeight
public import Physlib.ClassicalFieldTheory.GaugeTheory.LocalFieldAlgebra.Sector
public import Physlib.Meta.Linters.Sorry
/-!

# The Standard Model challenge

## i. Overview

The classification of the Standard Model Lagrangian, stated so that every notion in it is
either the card `Physlib.Particles.StandardModel.Basic` or generic: the left side is the
submodule of gauge and Lorentz invariants of mass weight at most a bound, in the local
field algebra of the card's field datum (`GaugeFieldData.invariantsLE`), and the right
side is the span of the Lagrangian terms, each built by a generic constructor from the
card's fields. The challenge is to prove the statements in this form, with no
Standard-Model-specific definition entering the statement and, eventually, none entering
the proof beyond theorems about the card.

Each classification is stated element by element, as the existing theorems are: an element
of the filtration `massWeightSubmoduleLE w` fixed by every jet of gauge transformations and
by every Lorentz transformation is exactly a combination of the named terms.

The classification is currently proved in `AlgebraRealization/MassWeight/Filtration.lean`
in a form whose statement uses the hand-built realization, sector and span definitions of
this folder. Bridging the two forms is the remaining work; the statements below are its
target.

What can be stated today: the classification up to mass weight seven, where the only
invariants are the constant term and the Higgs mass term `H† H`, the latter by the generic
contraction `bosonNormSq` through the Higgs basis; the classification of the single
sectors up to mass weight eight, through the generic sector subalgebras; the triviality of
the central `ℤ₆` of the gauge group on every field; and the freeness of the gauge data.
The full classification up to mass weight eight needs generic constructors that do not
exist yet: the kinetic term of a fermion species, the field strength squared of each gauge
factor, the covariant-derivative and box terms of a scalar, the quartic potential, and the
Yukawa term of a fermion–fermion–scalar triple. Each is a contraction of the species'
indices, one delta or epsilon per gauge factor and a Lorentz contraction, read off the
charges. Two further results of the folder are outside the local field algebra and need
their own generic notions: anomaly cancellation (generic anomaly coefficients of a
table) and the minimisation of the Higgs potential (a generic scalar potential of a
datum).

## ii. Key results

- `StandardModel.Model.higgsMass_mem_massWeightSubmodule` : the Higgs mass term has mass
  weight four, from the card and the generic filtration alone.
- `StandardModel.Model.invariantsLE_four`, `invariantsLE_seven` : the classification up
  to mass weight four and seven.
- `StandardModel.Model.scalarSector_invariantsLE_eight`,
  `fermionSector_invariantsLE_eight`, `gaugeSector_invariantsLE_seven` : the
  single-sector classifications.
- `StandardModel.Model.repJet_ofConstant_eq_one_of_center` : the central `ℤ₆` acts
  trivially on every field.
- `StandardModel.Model.gaugeData_free` : the gauge data is free.

## iii. Table of contents

- A. The Higgs mass term
- B. The classification below mass weight eight
- C. The single sectors
- D. The centre of the gauge group
- E. Freeness of the gauge data

-/

@[expose] public section

open LocalGaugeData GaugeFieldData Matrix MatrixGroups

namespace StandardModel

namespace Model

/-!

## A. The Higgs mass term

-/

/-- The Higgs mass term `H† H`: the generic contraction of the Higgs with its conjugate
  through the Higgs basis. -/
local macro "higgsMass" : term =>
  `(fieldData.bosonNormSq ⟨⟨.H, by decide⟩, ⟨0, by decide⟩⟩ higgs.basis)

/-- **The Higgs mass term `H† H` has mass weight four**: a first check that the generic
  filtration computes on a term built from the card. -/
lemma higgsMass_mem_massWeightSubmodule :
    fieldData.bosonNormSq ⟨⟨.H, by decide⟩, ⟨0, by decide⟩⟩ higgs.basis
      ∈ fieldData.massWeightSubmodule 4 := by
  rw [mem_massWeightSubmodule_iff]
  intro c
  simp only [bosonNormSq, map_sum, map_mul, conjBosonSymbol, bosonSymbol, conjBosonSymbolMap,
    bosonSymbolMap, LinearMap.comp_apply, TensorProduct.mk_apply, LinearMap.inl_apply,
    LinearMap.inr_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hw : (fieldData.boson ⟨⟨.H, by decide⟩, ⟨0, by decide⟩⟩).massWeight = 2 := rfl
  erw [massWeightScale_ιBoson, massWeightScale_ιBoson, hw]
  simp only [JetComponentSpace.massWeightScale, LinearMap.smul_apply, LinearMap.prodMap_apply,
    TensorProduct.map_tmul, AlgHom.toLinearMap_apply, DerivAlgebraComplex.gradeScale_basis,
    Multiset.card_zero, pow_zero, one_smul, LinearMap.id_apply, map_zero, map_smul,
    smul_mul_smul_comm, ← pow_add]

/-!

## B. The classification below mass weight eight

-/

/-- **The challenge at mass weight four**: an element of the local field algebra of the
  Standard Model of mass weight at most four is fixed by every jet of gauge transformations
  and by every Lorentz transformation exactly when it is a combination of the constant term
  and the Higgs mass term `H† H`. -/
@[sorryful]
theorem invariantsLE_four (x : fieldData.LocalFieldAlgebra) :
    (x ∈ fieldData.massWeightSubmoduleLE 4
        ∧ (∀ U : Factors.G gauge, fieldData.repJet U x = x)
        ∧ ∀ Λ : SL(2,ℂ), fieldData.repLorentzGroup Λ x = x)
      ↔ x ∈ ℂ ∙ (1 : fieldData.LocalFieldAlgebra) ⊔ ℂ ∙ higgsMass := by
  sorry

/-- **The challenge below mass weight eight**: no invariant of mass weight five, six or
  seven exists, so an element of mass weight at most seven fixed by both groups is still a
  combination of the constant term and the Higgs mass term. -/
@[sorryful]
theorem invariantsLE_seven (x : fieldData.LocalFieldAlgebra) :
    (x ∈ fieldData.massWeightSubmoduleLE 7
        ∧ (∀ U : Factors.G gauge, fieldData.repJet U x = x)
        ∧ ∀ Λ : SL(2,ℂ), fieldData.repLorentzGroup Λ x = x)
      ↔ x ∈ ℂ ∙ (1 : fieldData.LocalFieldAlgebra) ⊔ ℂ ∙ higgsMass := by
  sorry

/-!

## C. The single sectors

The invariants built from one category of fields alone, through the generic sector
subalgebras. Without the connection no derivative of a matter field is gauge covariant,
so the scalar sector has only the powers of `H† H`, the fermion sector only the constants,
and the gauge sector nothing below the field strength squared at mass weight eight.

-/

/-- **The scalar sector up to mass weight eight**: an element built from the Higgs alone,
  of mass weight at most eight and fixed by both groups, is a combination of `1`, `H† H`
  and `(H† H)²`. -/
@[sorryful]
theorem scalarSector_invariantsLE_eight (x : fieldData.LocalFieldAlgebra) :
    (x ∈ fieldData.massWeightSubmoduleLE 8 ∧ x ∈ fieldData.SectorAlgebra {.scalar}
        ∧ (∀ U : Factors.G gauge, fieldData.repJet U x = x)
        ∧ ∀ Λ : SL(2,ℂ), fieldData.repLorentzGroup Λ x = x)
      ↔ x ∈ ℂ ∙ (1 : fieldData.LocalFieldAlgebra) ⊔ ℂ ∙ higgsMass
          ⊔ ℂ ∙ (higgsMass * higgsMass) := by
  sorry

/-- **The fermion sector up to mass weight eight**: an element built from the fermions
  alone, of mass weight at most eight and fixed by both groups, is a constant. -/
@[sorryful]
theorem fermionSector_invariantsLE_eight (x : fieldData.LocalFieldAlgebra) :
    (x ∈ fieldData.massWeightSubmoduleLE 8 ∧ x ∈ fieldData.SectorAlgebra {.fermion}
        ∧ (∀ U : Factors.G gauge, fieldData.repJet U x = x)
        ∧ ∀ Λ : SL(2,ℂ), fieldData.repLorentzGroup Λ x = x)
      ↔ x ∈ ℂ ∙ (1 : fieldData.LocalFieldAlgebra) := by
  sorry

/-- **The gauge sector below mass weight eight**: an element built from the gauge fields
  alone, of mass weight at most seven and fixed by both groups, is a constant. -/
@[sorryful]
theorem gaugeSector_invariantsLE_seven (x : fieldData.LocalFieldAlgebra) :
    (x ∈ fieldData.massWeightSubmoduleLE 7 ∧ x ∈ fieldData.SectorAlgebra {.gauge}
        ∧ (∀ U : Factors.G gauge, fieldData.repJet U x = x)
        ∧ ∀ Λ : SL(2,ℂ), fieldData.repLorentzGroup Λ x = x)
      ↔ x ∈ ℂ ∙ (1 : fieldData.LocalFieldAlgebra) := by
  sorry

/-!

## D. The centre of the gauge group

-/

/-- **The central `ℤ₆` acts trivially on every field**: a gauge transformation whose
  components are `ζ² 1₃`, `ζ³ 1₂` and `ζ` for a sixth root of unity `ζ` fixes the jets
  of every fermionic and bosonic species, since the hypercharges are `6 Y` and every
  field has `2 · (colour triality) + 3 · (isospin duality) + 6 Y ≡ 0 (mod 6)`. -/
@[sorryful]
theorem repJet_ofConstant_eq_one_of_center (ζ : ℂ) (hζ : ζ ^ 6 = 1) (g : Factors.G₀ gauge)
    (h₃ : (g.1 : specialUnitaryGroup (Fin 3) ℂ).1 = ζ ^ 2 • (1 : Matrix (Fin 3) (Fin 3) ℂ))
    (h₂ : (g.2.1 : specialUnitaryGroup (Fin 2) ℂ).1 = ζ ^ 3 • (1 : Matrix (Fin 2) (Fin 2) ℂ))
    (h₁ : (g.2.2 : unitary ℂ).1 = ζ) :
    (∀ i, (fieldData.fermion i).repJet (gaugeData.ofConstant g) = 1)
      ∧ ∀ j, (fieldData.boson j).repJet (gaugeData.ofConstant g) = 1 := by
  sorry

/-!

## E. Freeness of the gauge data

-/

/-- **The gauge data of the Standard Model is free**: every Taylor family of gauge algebra
  elements is realised by a jet, and every jet of gauge algebra elements vanishing at the
  base point is the radial Maurer–Cartan component of a pure jet. Proved by hand for the
  hand-built gauge data in `GaugeGroup/MaurerCartan/Freeness.lean`; the challenge is the
  generic proof, factor by factor, for `ofFactors`. -/
@[sorryful]
theorem gaugeData_free : gaugeData.Free := by
  sorry

end Model

end StandardModel
