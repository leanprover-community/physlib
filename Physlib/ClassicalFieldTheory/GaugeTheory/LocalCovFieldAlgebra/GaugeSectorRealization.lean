/-
Copyright (c) 2026 Nathaneal Sajan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaneal Sajan
-/
module

public import Physlib.ClassicalFieldTheory.GaugeTheory.GaugeBoson.LocalGaugeCovFieldAlgebra.Realization
public import Physlib.ClassicalFieldTheory.GaugeTheory.LocalCovFieldAlgebra.GaugeSector
public import Physlib.ClassicalFieldTheory.GaugeTheory.LocalCovFieldAlgebra.SectorRealization
public import Physlib.ClassicalFieldTheory.GaugeTheory.LocalFieldAlgebra.GaugeSectorRealization
/-!
# Realizations of the covariant gauge sector

## i. Overview

For a complex algebra `B`, realizations of the covariant gauge sector
`T.CovSectorAlgebra {FieldCategory.gauge}` are the real realizations of the covariant
gauge-only algebra `LocalGaugeCovFieldAlgebra 𝔤` in `B`, its gauge and Lorentz actions
viewed over `ℝ` by restriction of scalars. The correspondence is
`GaugeFieldData.covGaugeSectorEquiv` composed with `AlgHom.liftEquiv`, and the
field-strength towers agree on both sides.

`GaugeFieldData.GaugeLorentzCompatible` is carried only to name the source Lorentz action,
as on the sector realizations themselves. Restricting a realization of the whole local
field algebra to the covariant gauge sector and passing to the gauge-only side is the
covariant restriction of its ordinary gauge-only realization.

## ii. Key results

- `GaugeFieldData.covGaugeSectorRealizationEquiv` : the correspondence, with both round
  trips.
- `GaugeFieldData.covGaugeSectorRealizationEquiv_F`,
  `GaugeFieldData.covGaugeSectorRealizationEquiv_symm_toAlgHom_covF` : the field-strength
  towers of corresponding realizations.
- `GaugeFieldData.covGaugeSectorRealizationEquiv_restrictCovSector` : compatibility with
  restriction from the local field algebra.

## iii. Table of contents

- A. The correspondence
- B. Computation
- C. Compatibility with restriction

-/

@[expose] public section

open TensorProduct Matrix MatrixGroups

namespace GaugeFieldData

variable {G₀ : Type} [Group G₀] {𝔤 : Type} [LieRing 𝔤] [LieAlgebra ℝ 𝔤] [Module.Finite ℝ 𝔤]
  {GJ : Type} [Group GJ] {𝔤J : Type} [LieRing 𝔤J] [LieAlgebra ℝ 𝔤J]
  {jets : LocalGaugeData G₀ 𝔤 GJ 𝔤J} {T : GaugeFieldData jets} {B : Type} [Ring B]
  [Algebra ℂ B] {repGauge : Representation ℂ G₀ B} {repLorentz : Representation ℂ SL(2,ℂ) B}

/-!

## A. The correspondence

-/

variable (T) in
/-- Realizations of the covariant gauge sector are the real realizations of the covariant
  gauge-only algebra, the target keeping its complex actions restricted to `ℝ`. -/
noncomputable def covGaugeSectorRealizationEquiv (hGL : T.GaugeLorentzCompatible) :
    CovSectorAlgebra.Realization T {FieldCategory.gauge} hGL B repGauge repLorentz
      ≃ LocalGaugeCovFieldAlgebra.Realization jets B (repGauge.restrictScalars ℝ)
          (repLorentz.restrictScalars ℝ) :=
  (Representation.EquivariantAlgHom.compEquiv T.covGaugeSectorEquiv
      covGaugeSectorEquiv_complexRepValue
      (covGaugeSectorEquiv_complexRepLorentzGroup hGL)).trans
    (Representation.EquivariantAlgHom.liftEquivBaseChange
      LocalGaugeCovFieldAlgebra.complexRepValue_tmul
      LocalGaugeCovFieldAlgebra.complexRepLorentzGroup_tmul).symm

/-!

## B. Computation

-/

variable (hGL : T.GaugeLorentzCompatible)

lemma covGaugeSectorRealizationEquiv_toAlgHom
    (k : CovSectorAlgebra.Realization T {FieldCategory.gauge} hGL B repGauge repLorentz) :
    (T.covGaugeSectorRealizationEquiv hGL k).toAlgHom
      = ((k.toAlgHom.comp T.covGaugeSectorEquiv.toAlgHom).restrictScalars ℝ).comp
          Algebra.TensorProduct.includeRight := rfl

@[simp]
lemma covGaugeSectorRealizationEquiv_toAlgHom_apply
    (k : CovSectorAlgebra.Realization T {FieldCategory.gauge} hGL B repGauge repLorentz)
    (x : LocalGaugeCovFieldAlgebra 𝔤) :
    (T.covGaugeSectorRealizationEquiv hGL k).toAlgHom x
      = k.toAlgHom (T.covGaugeSectorEquiv ((1 : ℂ) ⊗ₜ[ℝ] x)) := rfl

/-- The field-strength tower of the corresponding real realization is the sector tower,
  with the same derivative labels, spacetime indices and adjoint covector. -/
lemma covGaugeSectorRealizationEquiv_F
    (k : CovSectorAlgebra.Realization T {FieldCategory.gauge} hGL B repGauge repLorentz)
    (l : List (Fin 1 ⊕ Fin 3)) (μ ν : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ 𝔤) :
    (T.covGaugeSectorRealizationEquiv hGL k).F l μ ν φ
      = k.toAlgHom
          (T.covGaugeSectorEquiv ((1 : ℂ) ⊗ₜ[ℝ] LocalGaugeCovFieldAlgebra.covF 𝔤 l μ ν φ)) :=
  rfl

lemma covGaugeSectorRealizationEquiv_symm_toAlgHom
    (h : LocalGaugeCovFieldAlgebra.Realization jets B (repGauge.restrictScalars ℝ)
      (repLorentz.restrictScalars ℝ)) :
    ((T.covGaugeSectorRealizationEquiv hGL).symm h).toAlgHom
      = (AlgHom.liftEquiv ℝ ℂ (LocalGaugeCovFieldAlgebra 𝔤) B h.toAlgHom).comp
          T.covGaugeSectorEquiv.symm.toAlgHom := rfl

@[simp]
lemma covGaugeSectorRealizationEquiv_symm_toAlgHom_apply
    (h : LocalGaugeCovFieldAlgebra.Realization jets B (repGauge.restrictScalars ℝ)
      (repLorentz.restrictScalars ℝ)) (x : T.CovSectorAlgebra {FieldCategory.gauge}) :
    ((T.covGaugeSectorRealizationEquiv hGL).symm h).toAlgHom x
      = AlgHom.liftEquiv ℝ ℂ (LocalGaugeCovFieldAlgebra 𝔤) B h.toAlgHom
          (T.covGaugeSectorEquiv.symm x) := rfl

/-- The sector towers of the corresponding sector realization are the tower of the real
  realization; at `l = []` this is the field strength. -/
lemma covGaugeSectorRealizationEquiv_symm_toAlgHom_covF
    (h : LocalGaugeCovFieldAlgebra.Realization jets B (repGauge.restrictScalars ℝ)
      (repLorentz.restrictScalars ℝ)) (l : List (Fin 1 ⊕ Fin 3)) (μ ν : Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℝ 𝔤) :
    ((T.covGaugeSectorRealizationEquiv hGL).symm h).toAlgHom
        (T.covGaugeSectorEquiv ((1 : ℂ) ⊗ₜ[ℝ] LocalGaugeCovFieldAlgebra.covF 𝔤 l μ ν φ))
      = h.F l μ ν φ :=
  calc ((T.covGaugeSectorRealizationEquiv hGL).symm h).toAlgHom
        (T.covGaugeSectorEquiv ((1 : ℂ) ⊗ₜ[ℝ] LocalGaugeCovFieldAlgebra.covF 𝔤 l μ ν φ))
      = AlgHom.liftEquiv ℝ ℂ (LocalGaugeCovFieldAlgebra 𝔤) B h.toAlgHom
          ((1 : ℂ) ⊗ₜ[ℝ] LocalGaugeCovFieldAlgebra.covF 𝔤 l μ ν φ) :=
        congrArg _ (T.covGaugeSectorEquiv.symm_apply_apply _)
    _ = h.F l μ ν φ := by
        rw [AlgHom.liftEquiv_tmul, one_smul, LocalGaugeCovFieldAlgebra.Realization.F_apply]

/-!

## C. Compatibility with restriction

-/

set_option maxHeartbeats 400000 in
/-- Restricting a realization of the local field algebra to the covariant gauge sector and
  passing to the gauge-only side gives the covariant restriction of its ordinary gauge-only
  realization. -/
lemma covGaugeSectorRealizationEquiv_restrictCovSector
    {repJet : Representation ℂ GJ B} (h : Realization T B repJet repLorentz) :
    T.covGaugeSectorRealizationEquiv hGL (h.restrictCovSector hGL {FieldCategory.gauge})
      = (T.gaugeSectorRealizationEquiv (h.restrictSector {FieldCategory.gauge})).restrict :=
  Representation.EquivariantAlgHom.ext (AlgHom.ext fun x => by
    rw [covGaugeSectorRealizationEquiv_toAlgHom_apply,
      Realization.restrictCovSector_toAlgHom_apply,
      LocalGaugeFieldAlgebra.Realization.restrict_toAlgHom_apply,
      gaugeSectorRealizationEquiv_toAlgHom_apply, Realization.restrictSector_toAlgHom_apply,
      coe_covGaugeSectorEquiv, coe_gaugeSectorEquiv, includeCovConnection_one_tmul])

end GaugeFieldData
