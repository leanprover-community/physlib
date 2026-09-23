/-
Copyright (c) 2026 Nathaneal Sajan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaneal Sajan
-/
module

public import Physlib.ClassicalFieldTheory.GaugeTheory.GaugeBoson.LocalGaugeFieldAlgebra.Realization
public import Physlib.ClassicalFieldTheory.GaugeTheory.LocalFieldAlgebra.GaugeSector
public import Physlib.ClassicalFieldTheory.GaugeTheory.LocalFieldAlgebra.SectorRealization
/-!
# Realizations of the ordinary gauge sector

## i. Overview

For a complex algebra `B`, realizations of the ordinary gauge sector
`T.SectorAlgebra {FieldCategory.gauge}` are the real realizations of the gauge-only algebra
`LocalGaugeFieldAlgebra 𝔤` in `B`, its two actions viewed over `ℝ` by restriction of
scalars. The correspondence is the algebra equivalence `GaugeFieldData.gaugeSectorEquiv`
composed with the universal property of base change `AlgHom.liftEquiv`; the gauge symbols
`∂_s A_μ^φ` agree on both sides.

## ii. Key results

- `GaugeFieldData.gaugeSectorRealizationEquiv` : the correspondence, with both round trips.
- `GaugeFieldData.gaugeSectorRealizationEquiv_A`,
  `GaugeFieldData.gaugeSectorRealizationEquiv_symm_toAlgHom_gaugeField` : the gauge symbols
  of corresponding realizations.

## iii. Table of contents

- A. The correspondence
- B. Computation

-/

@[expose] public section

open TensorProduct Matrix MatrixGroups

namespace GaugeFieldData

variable {G₀ : Type} [Group G₀] {𝔤 : Type} [LieRing 𝔤] [LieAlgebra ℝ 𝔤] [Module.Finite ℝ 𝔤]
  {GJ : Type} [Group GJ] {𝔤J : Type} [LieRing 𝔤J] [LieAlgebra ℝ 𝔤J]
  {jets : LocalGaugeData G₀ 𝔤 GJ 𝔤J} {T : GaugeFieldData jets} {B : Type} [Ring B]
  [Algebra ℂ B] {repJet : Representation ℂ GJ B} {repLorentz : Representation ℂ SL(2,ℂ) B}

/-!

## A. The correspondence

-/

variable (T) in
/-- Realizations of the ordinary gauge sector are the real realizations of the gauge-only
  algebra, the target keeping its complex actions restricted to `ℝ`. -/
noncomputable def gaugeSectorRealizationEquiv :
    SectorAlgebra.Realization T {FieldCategory.gauge} B repJet repLorentz
      ≃ LocalGaugeFieldAlgebra.Realization jets B (repJet.restrictScalars ℝ)
          (repLorentz.restrictScalars ℝ) :=
  (Representation.EquivariantAlgHom.compEquiv T.gaugeSectorEquiv
      gaugeSectorEquiv_complexRepJet gaugeSectorEquiv_complexRepLorentzGroup).trans
    (Representation.EquivariantAlgHom.liftEquivBaseChange
      LocalGaugeFieldAlgebra.complexRepJet_tmul
      LocalGaugeFieldAlgebra.complexRepLorentzGroup_tmul).symm

/-!

## B. Computation

-/

lemma gaugeSectorRealizationEquiv_toAlgHom
    (f : SectorAlgebra.Realization T {FieldCategory.gauge} B repJet repLorentz) :
    (T.gaugeSectorRealizationEquiv f).toAlgHom
      = ((f.toAlgHom.comp T.gaugeSectorEquiv.toAlgHom).restrictScalars ℝ).comp
          Algebra.TensorProduct.includeRight := rfl

@[simp]
lemma gaugeSectorRealizationEquiv_toAlgHom_apply
    (f : SectorAlgebra.Realization T {FieldCategory.gauge} B repJet repLorentz)
    (x : LocalGaugeFieldAlgebra 𝔤) :
    (T.gaugeSectorRealizationEquiv f).toAlgHom x
      = f.toAlgHom (T.gaugeSectorEquiv ((1 : ℂ) ⊗ₜ[ℝ] x)) := rfl

/-- The gauge symbols of the corresponding real realization are the sector symbols. -/
lemma gaugeSectorRealizationEquiv_A
    (f : SectorAlgebra.Realization T {FieldCategory.gauge} B repJet repLorentz)
    (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ 𝔤) :
    (T.gaugeSectorRealizationEquiv f).A s μ φ
      = f.toAlgHom (T.gaugeSectorEquiv (LocalGaugeFieldAlgebra.gaugeField 𝔤 s μ φ)) :=
  (congrArg (fun y => f.toAlgHom (T.gaugeSectorEquiv y))
    (LocalGaugeFieldAlgebra.gaugeField_eq_one_tmul_derivA s μ φ)).symm

lemma gaugeSectorRealizationEquiv_symm_toAlgHom
    (h : LocalGaugeFieldAlgebra.Realization jets B (repJet.restrictScalars ℝ)
      (repLorentz.restrictScalars ℝ)) :
    (T.gaugeSectorRealizationEquiv.symm h).toAlgHom
      = (AlgHom.liftEquiv ℝ ℂ (LocalGaugeFieldAlgebra 𝔤) B h.toAlgHom).comp
          T.gaugeSectorEquiv.symm.toAlgHom := rfl

@[simp]
lemma gaugeSectorRealizationEquiv_symm_toAlgHom_apply
    (h : LocalGaugeFieldAlgebra.Realization jets B (repJet.restrictScalars ℝ)
      (repLorentz.restrictScalars ℝ)) (x : T.SectorAlgebra {FieldCategory.gauge}) :
    (T.gaugeSectorRealizationEquiv.symm h).toAlgHom x
      = AlgHom.liftEquiv ℝ ℂ (LocalGaugeFieldAlgebra 𝔤) B h.toAlgHom
          (T.gaugeSectorEquiv.symm x) := rfl

/-- The sector symbols of the corresponding sector realization are the gauge symbols. -/
lemma gaugeSectorRealizationEquiv_symm_toAlgHom_gaugeField
    (h : LocalGaugeFieldAlgebra.Realization jets B (repJet.restrictScalars ℝ)
      (repLorentz.restrictScalars ℝ)) (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℝ 𝔤) :
    (T.gaugeSectorRealizationEquiv.symm h).toAlgHom
        (T.gaugeSectorEquiv (LocalGaugeFieldAlgebra.gaugeField 𝔤 s μ φ)) = h.A s μ φ :=
  calc (T.gaugeSectorRealizationEquiv.symm h).toAlgHom
        (T.gaugeSectorEquiv (LocalGaugeFieldAlgebra.gaugeField 𝔤 s μ φ))
      = AlgHom.liftEquiv ℝ ℂ (LocalGaugeFieldAlgebra 𝔤) B h.toAlgHom
          (LocalGaugeFieldAlgebra.gaugeField 𝔤 s μ φ) :=
        congrArg _ (T.gaugeSectorEquiv.symm_apply_apply _)
    _ = h.A s μ φ := by
        rw [LocalGaugeFieldAlgebra.gaugeField_eq_one_tmul_derivA, AlgHom.liftEquiv_tmul,
          one_smul, LocalGaugeFieldAlgebra.Realization.A_apply]

end GaugeFieldData
