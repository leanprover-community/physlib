/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.Particles.StandardModel.LocalFieldAlgebra.LocalCovFieldAlgebra.Sectors
public import PhyslibAlpha.Particles.StandardModel.LocalFieldAlgebra.ScalarSector.MassWeight.Basic
/-!
# The mixed gauge-Higgs sector

The gauge-Higgs sector of the Standard Model's covariant field algebra, as a join of products.

## i. Overview

Everything below is stated about the covariant field algebra `fieldData.LocalCovFieldAlgebra` of the
Standard Model.

The field-strength towers are bosonic, so they commute with every Higgs tower
(`LocalCovFieldAlgebra.F_comm_H`, `LocalCovFieldAlgebra.F_comm_barH`). Consequently the gauge
algebra and the Higgs algebra commute (`commute_of_mem_gaugeAlgebra_of_mem_higgsAlgebra`), and so do
their mass-weight submodules in either order (`higgsMassWeight_mul_gaugeMassWeight_le`). Feeding
this into the abstract two-class bound `sectorMassWeight_pair_le` gives the mixed `{gauge, scalar}`
sector's weight-`w` piece as a join, over the splittings of `w` into two non-zero parts, of products
of the two sectors' own mass-weight submodules (`sectorMassWeight_gauge_higgs_le`).

Both a non-zero gauge weight and a non-zero Higgs weight are even, and they are at
least `4` and `2` respectively. So the mixed sector vanishes below weight `6` and at
every odd weight. At weight `6` it is exactly the underived field strength against the
underived Higgs, and at weight `8` it is bounded by the field strength against the
weight-four Higgs terms together with the once-derived field strength against the
underived Higgs.

## ii. Key results

- `commute_of_mem_gaugeAlgebra_of_mem_higgsAlgebra` : the gauge algebra and the Higgs algebra
  commute element-wise.
- `sectorMassWeight_gauge_higgs_le` : the mixed gauge-Higgs sector as a join of products.
- `sectorMassWeight_gauge_higgs_six`, `sectorMassWeight_gauge_higgs_eight` : the mixed sector at
  weights six and eight.

## iii. Table of contents

- A. The mixed gauge-Higgs sector

## iv. References

* None.

-/

/-!

## A. The mixed gauge-Higgs sector

-/

@[expose] public section

namespace StandardModel

open GaugeFieldData (FieldKind)

open TensorProduct Matrix MatrixGroups Lorentz


namespace LocalCovFieldAlgebra

/-- The gauge algebra and the Higgs algebra commute element-wise. -/
lemma commute_of_mem_gaugeAlgebra_of_mem_higgsAlgebra {x y : fieldData.LocalCovFieldAlgebra}
    (hx : x ∈ GaugeSector.gaugeAlgebra) (hy : y ∈ ScalarSector.higgsAlgebra) :
    Commute x y := by
  have hgen : ∀ a ∈ (⋃ (n : ℕ) (l : Fin n → Fin 1 ⊕ Fin 3) (μ : Fin 1 ⊕ Fin 3)
        (ν : Fin 1 ⊕ Fin 3), Set.range (gaugeFieldStrength l μ ν)),
      ∀ b ∈ (⋃ (k : ℕ) (dd : Fin k → (Fin 1 ⊕ Fin 3)),
        Set.range (higgsField dd) ∪ Set.range (conjHiggsField dd)),
          Commute a b := by
    intro a ha b hb
    simp only [Set.mem_iUnion, Set.mem_range] at ha
    obtain ⟨n, l, μ, ν, φ, rfl⟩ := ha
    simp only [Set.mem_iUnion, Set.mem_union, Set.mem_range] at hb
    obtain ⟨k, dd, (⟨φ', rfl⟩ | ⟨φ', rfl⟩)⟩ := hb
    · exact LocalCovFieldAlgebra.F_comm_H l μ ν φ dd φ'
    · exact LocalCovFieldAlgebra.F_comm_barH l μ ν φ dd φ'
  rw [GaugeSector.gaugeAlgebra] at hx
  rw [ScalarSector.higgsAlgebra] at hy
  refine Algebra.commute_of_mem_adjoin_of_forall_mem_commute hy fun b hb => ?_
  exact (Algebra.commute_of_mem_adjoin_of_forall_mem_commute hx
    fun a ha => (hgen a ha b hb).symm).symm

/-- The Higgs and gauge mass-weight submodules commute past each other. -/
lemma higgsMassWeight_mul_gaugeMassWeight_le (a b : ℕ) :
    ScalarSector.massWeightSubmodule a * GaugeSector.massWeightSubmodule b
      ≤ GaugeSector.massWeightSubmodule b * ScalarSector.massWeightSubmodule a := by
  refine Submodule.mul_le.mpr fun x hx y hy => ?_
  rw [(LocalCovFieldAlgebra.commute_of_mem_gaugeAlgebra_of_mem_higgsAlgebra
    (GaugeSector.mem_gaugeAlgebra_of_mem_massWeightSubmodule hy)
    (ScalarSector.mem_higgsAlgebra_of_mem_massWeightSubmodule hx)).symm.eq]
  exact Submodule.mul_mem_mul hy hx

/-- The mixed gauge-Higgs sector decomposition. -/
lemma sectorMassWeight_gauge_higgs_le (w : ℕ) :
    fieldData.sectorMassWeight {FieldKind.gauge, FieldKind.scalar} w
      ≤ ⨆ (p : ℕ × ℕ) (_ : p.1 + p.2 = w) (_ : p.1 ≠ 0) (_ : p.2 ≠ 0),
        GaugeSector.massWeightSubmodule p.1 * ScalarSector.massWeightSubmodule p.2 :=
  GaugeFieldData.sectorMassWeight_pair_le LocalCovFieldAlgebra.hasPositiveMassWeights
    (c₁ := FieldKind.gauge) (c₂ := FieldKind.scalar)
    (M₁ := GaugeSector.massWeightSubmodule) (M₂ := ScalarSector.massWeightSubmodule)
    (by decide)
    (fun w => LocalCovFieldAlgebra.sectorMassWeight_gauge_le w)
      (fun w => LocalCovFieldAlgebra.sectorMassWeight_higgs_le w)
    GaugeSector.one_le_massWeightSubmodule_zero
    ScalarSector.one_le_massWeightSubmodule_zero
    (fun a b => GaugeSector.massWeightSubmodule_mul_le a b)
    (fun a b => ScalarSector.massWeightSubmodule_mul_le a b)
    (fun a b => LocalCovFieldAlgebra.higgsMassWeight_mul_gaugeMassWeight_le a b) w

/-- The mixed gauge-Higgs sector vanishes below weight `6`. -/
lemma sectorMassWeight_gauge_higgs_eq_bot_of_lt_six {w : ℕ} (hw : w < 6) :
    fieldData.sectorMassWeight {FieldKind.gauge, FieldKind.scalar} w = ⊥ := by
  have ho : ∀ k : ℕ, Odd k → ScalarSector.massWeightSubmodule k = ⊥ :=
    fun k hk => ScalarSector.massWeightSubmodule_odd_eq_bot k hk
  refine le_bot_iff.mp ((LocalCovFieldAlgebra.sectorMassWeight_gauge_higgs_le w).trans ?_)
  refine iSup_le fun p => iSup_le fun hp => iSup_le fun h1 => iSup_le fun h2 => ?_
  obtain ⟨a, b⟩ := p
  dsimp only at hp h1 h2 ⊢
  have ha : a ≤ 5 := by omega
  have hb : b ≤ 5 := by omega
  interval_cases a <;> interval_cases b <;>
    first
      | omega
      | simp [GaugeSector.massWeightSubmodule_one_eq,
          GaugeSector.massWeightSubmodule_two_eq,
          GaugeSector.massWeightSubmodule_three_eq,
          ho 1 (by decide), ho 3 (by decide)]

/-- The mixed gauge-Higgs sector vanishes at weight `7`, since both a gauge weight and a
  Higgs weight are even, so they cannot sum to an odd number. -/
lemma sectorMassWeight_gauge_higgs_seven :
    fieldData.sectorMassWeight {FieldKind.gauge, FieldKind.scalar} 7 = ⊥ := by
  have ho : ∀ k : ℕ, Odd k → ScalarSector.massWeightSubmodule k = ⊥ :=
    fun k hk => ScalarSector.massWeightSubmodule_odd_eq_bot k hk
  refine le_bot_iff.mp ((LocalCovFieldAlgebra.sectorMassWeight_gauge_higgs_le 7).trans ?_)
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
          ho 1 (by decide), ho 3 (by decide), ho 5 (by decide)]

/-- The mixed gauge-Higgs sector at weight `6` is exactly the product of the
  underived field strength with the underived Higgs, the only surviving splitting being
  `4 + 2`. -/
lemma sectorMassWeight_gauge_higgs_six :
    fieldData.sectorMassWeight {FieldKind.gauge, FieldKind.scalar} 6
      = GaugeSector.derivSubmodule 0 * ScalarSector.derivSubmodule 0 := by
  have ho : ∀ k : ℕ, Odd k → ScalarSector.massWeightSubmodule k = ⊥ :=
    fun k hk => ScalarSector.massWeightSubmodule_odd_eq_bot k hk
  refine le_antisymm ?_ ?_
  · refine (LocalCovFieldAlgebra.sectorMassWeight_gauge_higgs_le 6).trans
      (iSup_le fun p => iSup_le fun hp => iSup_le fun h1 => iSup_le fun h2 => ?_)
    obtain ⟨a, b⟩ := p
    dsimp only at hp h1 h2 ⊢
    have ha : a ≤ 5 := by omega
    have hb : b ≤ 5 := by omega
    interval_cases a <;> interval_cases b <;>
      first
        | omega
        | simp [GaugeSector.massWeightSubmodule_one_eq,
            GaugeSector.massWeightSubmodule_two_eq,
            GaugeSector.massWeightSubmodule_three_eq,
            GaugeSector.massWeightSubmodule_four_eq,
            GaugeSector.massWeightSubmodule_five_eq,
            ScalarSector.massWeightSubmodule_two_eq_deriv,
            ho 1 (by decide), ho 3 (by decide), bot_le]
  · have hgauge : GaugeSector.derivSubmodule 0
        = fieldData.sectorMassWeight {FieldKind.gauge} 4 := by
      rw [← GaugeSector.massWeightSubmodule_four_eq,
        ← LocalCovFieldAlgebra.sectorMassWeight_gauge_eq (by norm_num)]
    have hhiggs : ScalarSector.derivSubmodule 0
        = fieldData.sectorMassWeight {FieldKind.scalar} 2 := by
      rw [← ScalarSector.massWeightSubmodule_two_eq_deriv,
        ← LocalCovFieldAlgebra.sectorMassWeight_higgs_eq (by norm_num)]
    rw [hgauge, hhiggs]
    have hset : ({FieldKind.gauge} ∪ {FieldKind.scalar} : Finset FieldKind)
        = {FieldKind.gauge, FieldKind.scalar} := by decide
    refine Submodule.mul_le.mpr fun x hx y hy => ?_
    have := GaugeFieldData.mul_mem_sectorMassWeight hx hy
    rwa [hset] at this

/-- A product of a gauge-weight piece and a Higgs-weight piece lands in the mixed
  sector of the total weight. -/
lemma mul_le_sectorMassWeight_gauge_higgs {a b w : ℕ}
    {X Y : Submodule ℂ fieldData.LocalCovFieldAlgebra}
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a + b = w)
    (hX : X ≤ GaugeSector.massWeightSubmodule a)
    (hY : Y ≤ ScalarSector.massWeightSubmodule b) :
    X * Y ≤ fieldData.sectorMassWeight {FieldKind.gauge, FieldKind.scalar} w := by
  have hset : ({FieldKind.gauge} ∪ {FieldKind.scalar} : Finset FieldKind)
      = {FieldKind.gauge, FieldKind.scalar} := by decide
  refine Submodule.mul_le.mpr fun x hx y hy => ?_
  have hx' : x ∈ fieldData.sectorMassWeight {FieldKind.gauge} a := by
    rw [LocalCovFieldAlgebra.sectorMassWeight_gauge_eq ha]; exact hX hx
  have hy' : y ∈ fieldData.sectorMassWeight {FieldKind.scalar} b := by
    rw [LocalCovFieldAlgebra.sectorMassWeight_higgs_eq hb]; exact hY hy
  have hmem := GaugeFieldData.mul_mem_sectorMassWeight hx' hy'
  rwa [hset, hab] at hmem

set_option synthInstance.maxHeartbeats 100000 in
/-- The mixed gauge-Higgs sector at weight `8`. The surviving splittings are
  `4 + 4` and `6 + 2`, giving the field strength against the weight-four Higgs terms
  and the once-derived field strength against the underived Higgs. -/
lemma sectorMassWeight_gauge_higgs_eight :
    fieldData.sectorMassWeight {FieldKind.gauge, FieldKind.scalar} 8
      = GaugeSector.derivSubmodule 0 * ScalarSector.derivSubmodule 1
        ⊔ GaugeSector.derivSubmodule 0 * ScalarSector.derivSubmodule 0
          * ScalarSector.derivSubmodule 0
        ⊔ GaugeSector.derivSubmodule 1 * ScalarSector.derivSubmodule 0 := by
  refine le_antisymm ?_ ?_
  case refine_2 =>
    refine sup_le (sup_le ?_ ?_) ?_
    · exact LocalCovFieldAlgebra.mul_le_sectorMassWeight_gauge_higgs (a := 4) (b := 4) (by norm_num)
        (by norm_num) (by norm_num) (le_of_eq GaugeSector.massWeightSubmodule_four_eq.symm)
        (by rw [ScalarSector.massWeightSubmodule_four_eq_deriv]; exact le_sup_left)
    · rw [mul_assoc]
      exact LocalCovFieldAlgebra.mul_le_sectorMassWeight_gauge_higgs (a := 4) (b := 4) (by norm_num)
        (by norm_num) (by norm_num) (le_of_eq GaugeSector.massWeightSubmodule_four_eq.symm)
        (by rw [ScalarSector.massWeightSubmodule_four_eq_deriv]; exact le_sup_right)
    · exact LocalCovFieldAlgebra.mul_le_sectorMassWeight_gauge_higgs (a := 6) (b := 2) (by norm_num)
        (by norm_num) (by norm_num) (le_of_eq GaugeSector.massWeightSubmodule_six_eq.symm)
        (le_of_eq ScalarSector.massWeightSubmodule_two_eq_deriv.symm)
  rw [mul_assoc]
  have ho : ∀ k : ℕ, Odd k → ScalarSector.massWeightSubmodule k = ⊥ :=
    fun k hk => ScalarSector.massWeightSubmodule_odd_eq_bot k hk
  refine (LocalCovFieldAlgebra.sectorMassWeight_gauge_higgs_le 8).trans
    (iSup_le fun p => iSup_le fun hp => iSup_le fun h1 => iSup_le fun h2 => ?_)
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
          GaugeSector.massWeightSubmodule_four_eq,
          GaugeSector.massWeightSubmodule_five_eq,
          GaugeSector.massWeightSubmodule_six_eq,
          GaugeSector.massWeightSubmodule_seven_eq,
          ScalarSector.massWeightSubmodule_two_eq_deriv,
          ScalarSector.massWeightSubmodule_four_eq_deriv, Submodule.mul_sup,
          ho 1 (by decide), ho 3 (by decide), ho 5 (by decide), ho 7 (by decide),
          bot_le]

end LocalCovFieldAlgebra

end StandardModel
