/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.Particles.StandardModel.LocalFieldAlgebra.LocalCovFieldAlgebra.Sectors
/-!
# The mixed gauge-fermion sector

The gauge-fermion sector of the Standard Model's covariant field algebra, as a join of products.

## i. Overview

Everything below is stated about the covariant field algebra `fieldData.LocalCovFieldAlgebra` of the
Standard Model.

The field-strength towers are bosonic, so they commute with every fermion tower
(`LocalCovFieldAlgebra.F_comm_d`, `LocalCovFieldAlgebra.F_comm_bard`, ...,
`LocalCovFieldAlgebra.F_comm_bare`). Consequently the gauge algebra
and the fermion algebra commute (`commute_of_mem_gaugeAlgebra_of_mem_fermionAlgebra`),
and so do their mass-weight submodules in either order
(`fermionMassWeight_mul_gaugeMassWeight_le`). Feeding this into the abstract two-class
sector bound `sectorMassWeight_pair_le` gives the mixed `{gauge, fermion}` sector's
weight-`w` piece as (the join over splittings of `w` into non-zero parts of) products
of the gauge and fermion sectors' own mass-weight submodules
(`sectorMassWeight_gauge_fermion_le`).

Since a non-zero gauge weight is at least `4` and a non-zero fermion weight is at
least `3`, the mixed sector vanishes below weight `7`
(`sectorMassWeight_gauge_fermion_eq_bot_of_lt_seven`) and at weight `8`
(`sectorMassWeight_gauge_fermion_eight`), and at weight `7` is exactly the product of
the underived field-strength submodule with the underived fermion submodule
(`sectorMassWeight_gauge_fermion_seven`).

## ii. Key results

- `commute_of_mem_gaugeAlgebra_of_mem_fermionAlgebra` : the gauge algebra and the fermion algebra
  commute element-wise.
- `sectorMassWeight_gauge_fermion_le` : the mixed gauge-fermion sector as a join of products.
- `sectorMassWeight_gauge_fermion_eq_bot_of_lt_seven`, `sectorMassWeight_gauge_fermion_eight` :
  the mixed sector vanishes below weight `7` and at weight `8`.
- `sectorMassWeight_gauge_fermion_seven` : the mixed sector at weight `7` is exactly the product
  of the underived field strength with the underived fermion towers.

## iii. Table of contents

- A. The gauge and fermion algebras commute
- B. The mixed gauge-fermion sector

## iv. References

* None.

-/

@[expose] public section

namespace StandardModel

open GaugeFieldData (FieldKind)

open TensorProduct Matrix MatrixGroups Lorentz


namespace LocalCovFieldAlgebra

/-!

## A. The gauge and fermion algebras commute

-/

/-- The gauge algebra and the fermion algebra commute element-wise. Every generator of
  the gauge algebra commutes with every generator of the fermion algebra by the
  commutation rules `LocalCovFieldAlgebra.F_comm_d`, ..., `LocalCovFieldAlgebra.F_comm_bare`,
  and commutation extends from generators to the algebras they generate. -/
lemma commute_of_mem_gaugeAlgebra_of_mem_fermionAlgebra {x y : fieldData.LocalCovFieldAlgebra}
    (hx : x ∈ GaugeSector.gaugeAlgebra) (hy : y ∈ FermionSector.fermionAlgebra) :
    Commute x y := by
  have hgen : ∀ a ∈ (⋃ (n : ℕ) (l : Fin n → Fin 1 ⊕ Fin 3) (μ : Fin 1 ⊕ Fin 3)
        (ν : Fin 1 ⊕ Fin 3), Set.range (gaugeFieldStrength l μ ν)),
      ∀ b ∈ (⋃ (i : Fin 3) (n : ℕ) (l : Fin n → Fin 1 ⊕ Fin 3),
        Set.range (downSingletField i l) ∪ Set.range
          (conjDownSingletField i l) ∪
        Set.range (upSingletField i l) ∪ Set.range (conjUpSingletField i
          l) ∪
        Set.range (quarkDoubletField i l) ∪ Set.range
          (conjQuarkDoubletField i l) ∪
        Set.range (leptonDoubletField i l) ∪ Set.range
          (conjLeptonDoubletField i l) ∪
        Set.range (leptonSingletField i l) ∪ Set.range
          (conjLeptonSingletField i l)), Commute a b := by
    intro a ha b hb
    simp only [Set.mem_iUnion, Set.mem_range] at ha
    obtain ⟨n, l, μ, ν, φ, rfl⟩ := ha
    simp only [Set.mem_iUnion, Set.mem_union, Set.mem_range] at hb
    obtain ⟨i, k, dd, (((((((((⟨φ', rfl⟩ | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) |
      ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩)⟩ := hb
    · exact LocalCovFieldAlgebra.F_comm_d l μ ν φ i dd φ'
    · exact LocalCovFieldAlgebra.F_comm_bard l μ ν φ i dd φ'
    · exact LocalCovFieldAlgebra.F_comm_u l μ ν φ i dd φ'
    · exact LocalCovFieldAlgebra.F_comm_baru l μ ν φ i dd φ'
    · exact LocalCovFieldAlgebra.F_comm_Q l μ ν φ i dd φ'
    · exact LocalCovFieldAlgebra.F_comm_barQ l μ ν φ i dd φ'
    · exact LocalCovFieldAlgebra.F_comm_L l μ ν φ i dd φ'
    · exact LocalCovFieldAlgebra.F_comm_barL l μ ν φ i dd φ'
    · exact LocalCovFieldAlgebra.F_comm_e l μ ν φ i dd φ'
    · exact LocalCovFieldAlgebra.F_comm_bare l μ ν φ i dd φ'
  rw [GaugeSector.gaugeAlgebra] at hx
  rw [FermionSector.fermionAlgebra] at hy
  refine Algebra.commute_of_mem_adjoin_of_forall_mem_commute hy fun b hb => ?_
  exact (Algebra.commute_of_mem_adjoin_of_forall_mem_commute hx
    fun a ha => (hgen a ha b hb).symm).symm

/-- The fermion sector's mass-weight submodules and the gauge sector's mass-weight
  submodules commute past each other, in the order needed by
  `sectorMassWeight_pair_le`. -/
lemma fermionMassWeight_mul_gaugeMassWeight_le (a b : ℕ) :
    FermionSector.massWeightSubmodule a * GaugeSector.massWeightSubmodule b
      ≤ GaugeSector.massWeightSubmodule b * FermionSector.massWeightSubmodule a := by
  refine Submodule.mul_le.mpr fun x hx y hy => ?_
  rw [(LocalCovFieldAlgebra.commute_of_mem_gaugeAlgebra_of_mem_fermionAlgebra
    (GaugeSector.mem_gaugeAlgebra_of_mem_massWeightSubmodule hy)
    (FermionSector.mem_fermionAlgebra_of_mem_massWeightSubmodule hx)).symm.eq]
  exact Submodule.mul_mem_mul hy hx

/-!

## B. The mixed gauge-fermion sector

-/

/-- The mixed gauge-fermion sector decomposition. The weight-`w` piece of the
  `{gauge, fermion}` sector lies in the join, over the splittings of `w` into two
  non-zero parts, of the products of the gauge and fermion sectors' own mass-weight
  submodules. -/
lemma sectorMassWeight_gauge_fermion_le (w : ℕ) :
    fieldData.sectorMassWeight {FieldKind.gauge, FieldKind.fermion} w
      ≤ ⨆ (p : ℕ × ℕ) (_ : p.1 + p.2 = w) (_ : p.1 ≠ 0) (_ : p.2 ≠ 0),
        GaugeSector.massWeightSubmodule p.1 * FermionSector.massWeightSubmodule p.2 :=
  GaugeFieldData.sectorMassWeight_pair_le LocalCovFieldAlgebra.hasPositiveMassWeights
    (c₁ := FieldKind.gauge) (c₂ := FieldKind.fermion)
    (M₁ := GaugeSector.massWeightSubmodule) (M₂ := FermionSector.massWeightSubmodule)
    (by decide)
    (fun w => LocalCovFieldAlgebra.sectorMassWeight_gauge_le w)
      (fun w => LocalCovFieldAlgebra.sectorMassWeight_fermion_le w)
    GaugeSector.one_le_massWeightSubmodule_zero
    FermionSector.one_le_massWeightSubmodule_zero
    (fun a b => GaugeSector.massWeightSubmodule_mul_le a b)
    (fun a b => FermionSector.massWeightSubmodule_mul_le a b)
    (fun a b => LocalCovFieldAlgebra.fermionMassWeight_mul_gaugeMassWeight_le a b) w

/-- The mixed gauge-fermion sector vanishes below weight `7`. A non-zero gauge
  weight is at least `4` and a non-zero fermion weight is at least `3`, so no
  splitting of a weight below `7` into two non-zero parts can supply both. -/
lemma sectorMassWeight_gauge_fermion_eq_bot_of_lt_seven {w : ℕ} (hw : w < 7) :
    fieldData.sectorMassWeight {FieldKind.gauge, FieldKind.fermion} w = ⊥ := by
  refine le_bot_iff.mp ((LocalCovFieldAlgebra.sectorMassWeight_gauge_fermion_le w).trans ?_)
  refine iSup_le fun p => iSup_le fun hp => iSup_le fun h1 => iSup_le fun h2 => ?_
  obtain ⟨a, b⟩ := p
  dsimp only at hp h1 h2 ⊢
  have ha : a ≤ 6 := by omega
  have hb : b ≤ 6 := by omega
  interval_cases a <;> interval_cases b <;>
    first
      | omega
      | simp [GaugeSector.massWeightSubmodule_one_eq,
          GaugeSector.massWeightSubmodule_two_eq,
          GaugeSector.massWeightSubmodule_three_eq,
          GaugeSector.massWeightSubmodule_five_eq,
          FermionSector.massWeightSubmodule_one_eq,
          FermionSector.massWeightSubmodule_two_eq,
          FermionSector.massWeightSubmodule_four_eq]

/-- The mixed gauge-fermion sector vanishes at weight `8`. The only splittings of
  `8` into two non-zero parts with a non-zero gauge weight and a non-zero fermion
  weight would need the gauge part to be `4` or `6` (with fermion part `4` or `2`), but
  the fermion sector vanishes at both `4` and `2`. -/
lemma sectorMassWeight_gauge_fermion_eight :
    fieldData.sectorMassWeight {FieldKind.gauge, FieldKind.fermion} 8 = ⊥ := by
  refine le_bot_iff.mp ((LocalCovFieldAlgebra.sectorMassWeight_gauge_fermion_le 8).trans ?_)
  refine iSup_le fun p => iSup_le fun hp => iSup_le fun h1 => iSup_le fun h2 => ?_
  obtain ⟨a, b⟩ := p
  dsimp only at hp h1 h2 ⊢
  have ha : a ≤ 7 := by omega
  have hb : b ≤ 7 := by omega
  interval_cases a <;> interval_cases b <;>
    first
      | omega
      | simp [GaugeSector.massWeightSubmodule_one_eq,
          GaugeSector.massWeightSubmodule_two_eq,
          GaugeSector.massWeightSubmodule_three_eq,
          GaugeSector.massWeightSubmodule_five_eq,
          GaugeSector.massWeightSubmodule_seven_eq,
          FermionSector.massWeightSubmodule_one_eq,
          FermionSector.massWeightSubmodule_two_eq,
          FermionSector.massWeightSubmodule_four_eq]

/-- The mixed gauge-fermion sector at weight `7` is exactly the product of the
  underived field-strength submodule with the underived fermion submodule, the only
  splitting of `7` into a non-zero gauge weight and a non-zero fermion weight that
  survives is `4 + 3`. -/
lemma sectorMassWeight_gauge_fermion_seven :
    fieldData.sectorMassWeight {FieldKind.gauge, FieldKind.fermion} 7
      = GaugeSector.derivSubmodule 0 * FermionSector.derivSubmodule 0 := by
  refine le_antisymm ?_ ?_
  · refine (LocalCovFieldAlgebra.sectorMassWeight_gauge_fermion_le 7).trans
      (iSup_le fun p => iSup_le fun hp => iSup_le fun h1 => iSup_le fun h2 => ?_)
    obtain ⟨a, b⟩ := p
    dsimp only at hp h1 h2 ⊢
    have ha : a ≤ 6 := by omega
    have hb : b ≤ 6 := by omega
    interval_cases a <;> interval_cases b <;>
      first
        | omega
        | simp [GaugeSector.massWeightSubmodule_one_eq,
            GaugeSector.massWeightSubmodule_two_eq,
            GaugeSector.massWeightSubmodule_three_eq,
            GaugeSector.massWeightSubmodule_four_eq,
            GaugeSector.massWeightSubmodule_five_eq,
            GaugeSector.massWeightSubmodule_six_eq,
            FermionSector.massWeightSubmodule_one_eq,
            FermionSector.massWeightSubmodule_two_eq,
            FermionSector.massWeightSubmodule_three_eq, bot_le]
  · have hgauge : GaugeSector.derivSubmodule 0 =
        fieldData.sectorMassWeight {FieldKind.gauge} 4 := by
      rw [← GaugeSector.massWeightSubmodule_four_eq, ←
        LocalCovFieldAlgebra.sectorMassWeight_gauge_eq
        (by norm_num)]
    have hfermion : FermionSector.derivSubmodule 0
        = fieldData.sectorMassWeight {FieldKind.fermion} 3 := by
      rw [← FermionSector.massWeightSubmodule_three_eq,
        ← LocalCovFieldAlgebra.sectorMassWeight_fermion_eq (by norm_num)]
    rw [hgauge, hfermion]
    have hset : ({FieldKind.gauge} ∪ {FieldKind.fermion} : Finset FieldKind)
        = {FieldKind.gauge, FieldKind.fermion} := by decide
    refine Submodule.mul_le.mpr fun x hx y hy => ?_
    have := GaugeFieldData.mul_mem_sectorMassWeight hx hy
    rwa [hset] at this

end LocalCovFieldAlgebra

end StandardModel
