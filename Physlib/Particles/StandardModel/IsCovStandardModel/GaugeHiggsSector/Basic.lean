/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.IsCovStandardModel.Sectors
public import Physlib.Particles.StandardModel.IsHiggsSector.MassWeight.Basic
/-!
# The mixed gauge-Higgs sector

The field-strength towers are bosonic, so they commute with every Higgs tower
(`h.F_comm_H`, `h.F_comm_barH`); consequently the gauge algebra and the Higgs algebra
commute (`commute_of_mem_gaugeAlgebra_of_mem_higgsAlgebra`), and so do their
mass-weight submodules in either order (`higgsMassWeight_mul_gaugeMassWeight_le`).
Feeding this into the abstract two-class bound `sectorMassWeight_pair_le` gives the
mixed `{gauge, higgs}` sector's weight-`w` piece as a join, over the splittings of `w`
into two non-zero parts, of products of the two sectors' own mass-weight submodules
(`sectorMassWeight_gauge_higgs_le`).

Both a non-zero gauge weight and a non-zero Higgs weight are even, and they are at
least `4` and `2` respectively.  So the mixed sector vanishes below weight `6` and at
every odd weight; at weight `6` it is exactly the underived field strength against the
underived Higgs, and at weight `8` it is bounded by the field strength against the
weight-four Higgs terms together with the once-derived field strength against the
underived Higgs.

-/

@[expose] public section

namespace StandardModel

open TensorProduct Matrix MatrixGroups Lorentz


namespace IsCovStandardModel

variable {B : Type} [Ring B] [Algebra ℂ B]
  {repGauge : Representation ℂ GaugeGroupI B}
  {hrepGauge_mul : ∀ (g : GaugeGroupI) (b₁ b₂ : B),
    repGauge g (b₁ * b₂) = repGauge g b₁ * repGauge g b₂}
  {repLorentz : Representation ℂ SL(2,ℂ) B}
  {hrepLorentz_mul : ∀ (Λ : SL(2,ℂ)) (b₁ b₂ : B),
    repLorentz Λ (b₁ * b₂) = repLorentz Λ b₁ * repLorentz Λ b₂}
  {massWeightPoly : B →ₐ[ℂ] Polynomial B}
  {H : {n : ℕ} → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ HiggsVec →ₗ[ℂ] B}
  {barH : {n : ℕ} → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ (ConjModule HiggsVec) →ₗ[ℂ] B}
  {F : {n : ℕ} → (Fin n → Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) →
    Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B}
  {d : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ DownSinglet →ₗ[ℂ] B}
  {bard : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ (ConjModule DownSinglet) →ₗ[ℂ] B}
  {u : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ UpSinglet →ₗ[ℂ] B}
  {baru : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ (ConjModule UpSinglet) →ₗ[ℂ] B}
  {Q : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ QuarkDoublet →ₗ[ℂ] B}
  {barQ : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ (ConjModule QuarkDoublet) →ₗ[ℂ] B}
  {L : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ LeptonDoublet →ₗ[ℂ] B}
  {barL : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ (ConjModule LeptonDoublet) →ₗ[ℂ] B}
  {e : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ LeptonSinglet →ₗ[ℂ] B}
  {bare : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ (ConjModule LeptonSinglet) →ₗ[ℂ] B}
  (h : IsCovStandardModel B repGauge hrepGauge_mul repLorentz hrepLorentz_mul
    massWeightPoly H barH F d bard u baru Q barQ L barL e bare)

/-- The gauge algebra and the Higgs algebra commute element-wise. -/
lemma commute_of_mem_gaugeAlgebra_of_mem_higgsAlgebra {x y : B}
    (hx : x ∈ h.isGaugeSector.gaugeAlgebra) (hy : y ∈ h.isHiggsSector.higgsAlgebra) :
    Commute x y := by
  have hgen : ∀ a ∈ (⋃ (n : ℕ) (l : Fin n → Fin 1 ⊕ Fin 3) (μ : Fin 1 ⊕ Fin 3)
        (ν : Fin 1 ⊕ Fin 3), Set.range (F l μ ν)),
      ∀ b ∈ (⋃ (k : ℕ) (dd : Fin k → (Fin 1 ⊕ Fin 3)),
        Set.range (H dd) ∪ Set.range (barH dd)), Commute a b := by
    intro a ha b hb
    simp only [Set.mem_iUnion, Set.mem_range] at ha
    obtain ⟨n, l, μ, ν, φ, rfl⟩ := ha
    simp only [Set.mem_iUnion, Set.mem_union, Set.mem_range] at hb
    obtain ⟨k, dd, (⟨φ', rfl⟩ | ⟨φ', rfl⟩)⟩ := hb
    · exact h.F_comm_H l μ ν φ dd φ'
    · exact h.F_comm_barH l μ ν φ dd φ'
  rw [IsGaugeSector.gaugeAlgebra] at hx
  rw [IsHiggsSector.higgsAlgebra] at hy
  refine Algebra.commute_of_mem_adjoin_of_forall_mem_commute hy fun b hb => ?_
  exact (Algebra.commute_of_mem_adjoin_of_forall_mem_commute hx
    fun a ha => (hgen a ha b hb).symm).symm

/-- The Higgs and gauge mass-weight submodules commute past each other. -/
lemma higgsMassWeight_mul_gaugeMassWeight_le (a b : ℕ) :
    h.isHiggsSector.massWeightSubmodule a * h.isGaugeSector.massWeightSubmodule b
      ≤ h.isGaugeSector.massWeightSubmodule b * h.isHiggsSector.massWeightSubmodule a := by
  refine Submodule.mul_le.mpr fun x hx y hy => ?_
  rw [(h.commute_of_mem_gaugeAlgebra_of_mem_higgsAlgebra
    (h.isGaugeSector.mem_gaugeAlgebra_of_mem_massWeightSubmodule hy)
    (h.isHiggsSector.mem_higgsAlgebra_of_mem_massWeightSubmodule hx)).symm.eq]
  exact Submodule.mul_mem_mul hy hx

/-- The mixed gauge-Higgs sector decomposition. -/
lemma sectorMassWeight_gauge_higgs_le (w : ℕ) :
    h.sectorMassWeight {GeneratorClass.gauge, GeneratorClass.higgs} w
      ≤ ⨆ (p : ℕ × ℕ) (_ : p.1 + p.2 = w) (_ : p.1 ≠ 0) (_ : p.2 ≠ 0),
        h.isGaugeSector.massWeightSubmodule p.1 * h.isHiggsSector.massWeightSubmodule p.2 :=
  h.sectorMassWeight_pair_le (c₁ := GeneratorClass.gauge) (c₂ := GeneratorClass.higgs)
    (M₁ := h.isGaugeSector.massWeightSubmodule) (M₂ := h.isHiggsSector.massWeightSubmodule)
    (by decide)
    (fun w => h.sectorMassWeight_gauge_le w) (fun w => h.sectorMassWeight_higgs_le w)
    h.isGaugeSector.one_le_massWeightSubmodule_zero
    h.isHiggsSector.one_le_massWeightSubmodule_zero
    (fun a b => h.isGaugeSector.massWeightSubmodule_mul_le a b)
    (fun a b => h.isHiggsSector.massWeightSubmodule_mul_le a b)
    (fun a b => h.higgsMassWeight_mul_gaugeMassWeight_le a b) w

/-- The mixed gauge-Higgs sector vanishes below weight `6`. -/
lemma sectorMassWeight_gauge_higgs_eq_bot_of_lt_six {w : ℕ} (hw : w < 6) :
    h.sectorMassWeight {GeneratorClass.gauge, GeneratorClass.higgs} w = ⊥ := by
  have ho : ∀ k : ℕ, Odd k → h.isHiggsSector.massWeightSubmodule k = ⊥ :=
    fun k hk => h.isHiggsSector.massWeightSubmodule_odd_eq_bot k hk
  refine le_bot_iff.mp ((h.sectorMassWeight_gauge_higgs_le w).trans ?_)
  refine iSup_le fun p => iSup_le fun hp => iSup_le fun h1 => iSup_le fun h2 => ?_
  obtain ⟨a, b⟩ := p
  dsimp only at hp h1 h2 ⊢
  have ha : a ≤ 5 := by omega
  have hb : b ≤ 5 := by omega
  interval_cases a <;> interval_cases b <;>
    first
      | omega
      | simp [h.isGaugeSector.massWeightSubmodule_one_eq,
          h.isGaugeSector.massWeightSubmodule_two_eq,
          h.isGaugeSector.massWeightSubmodule_three_eq,
          ho 1 (by decide), ho 3 (by decide)]

/-- The mixed gauge-Higgs sector vanishes at weight `7`: both a gauge weight and a
  Higgs weight are even, so they cannot sum to an odd number. -/
lemma sectorMassWeight_gauge_higgs_seven :
    h.sectorMassWeight {GeneratorClass.gauge, GeneratorClass.higgs} 7 = ⊥ := by
  have ho : ∀ k : ℕ, Odd k → h.isHiggsSector.massWeightSubmodule k = ⊥ :=
    fun k hk => h.isHiggsSector.massWeightSubmodule_odd_eq_bot k hk
  refine le_bot_iff.mp ((h.sectorMassWeight_gauge_higgs_le 7).trans ?_)
  refine iSup_le fun p => iSup_le fun hp => iSup_le fun h1 => iSup_le fun h2 => ?_
  obtain ⟨a, b⟩ := p
  dsimp only at hp h1 h2 ⊢
  have ha : a ≤ 6 := by omega
  have hb : b ≤ 6 := by omega
  interval_cases a <;> interval_cases b <;>
    first
      | omega
      | simp [h.isGaugeSector.massWeightSubmodule_one_eq,
          h.isGaugeSector.massWeightSubmodule_two_eq,
          h.isGaugeSector.massWeightSubmodule_three_eq,
          h.isGaugeSector.massWeightSubmodule_five_eq,
          ho 1 (by decide), ho 3 (by decide), ho 5 (by decide)]

/-- **The mixed gauge-Higgs sector at weight `6`** is exactly the product of the
  underived field strength with the underived Higgs: the only surviving splitting is
  `4 + 2`. -/
lemma sectorMassWeight_gauge_higgs_six :
    h.sectorMassWeight {GeneratorClass.gauge, GeneratorClass.higgs} 6
      = h.isGaugeSector.derivSubmodule 0 * h.isHiggsSector.derivSubmodule 0 := by
  have ho : ∀ k : ℕ, Odd k → h.isHiggsSector.massWeightSubmodule k = ⊥ :=
    fun k hk => h.isHiggsSector.massWeightSubmodule_odd_eq_bot k hk
  refine le_antisymm ?_ ?_
  · refine (h.sectorMassWeight_gauge_higgs_le 6).trans
      (iSup_le fun p => iSup_le fun hp => iSup_le fun h1 => iSup_le fun h2 => ?_)
    obtain ⟨a, b⟩ := p
    dsimp only at hp h1 h2 ⊢
    have ha : a ≤ 5 := by omega
    have hb : b ≤ 5 := by omega
    interval_cases a <;> interval_cases b <;>
      first
        | omega
        | simp [h.isGaugeSector.massWeightSubmodule_one_eq,
            h.isGaugeSector.massWeightSubmodule_two_eq,
            h.isGaugeSector.massWeightSubmodule_three_eq,
            h.isGaugeSector.massWeightSubmodule_four_eq,
            h.isGaugeSector.massWeightSubmodule_five_eq,
            h.isHiggsSector.massWeightSubmodule_two_eq_deriv,
            ho 1 (by decide), ho 3 (by decide), bot_le]
  · have hgauge : h.isGaugeSector.derivSubmodule 0
        = h.sectorMassWeight {GeneratorClass.gauge} 4 := by
      rw [← h.isGaugeSector.massWeightSubmodule_four_eq,
        ← h.sectorMassWeight_gauge_eq (by norm_num)]
    have hhiggs : h.isHiggsSector.derivSubmodule 0
        = h.sectorMassWeight {GeneratorClass.higgs} 2 := by
      rw [← h.isHiggsSector.massWeightSubmodule_two_eq_deriv,
        ← h.sectorMassWeight_higgs_eq (by norm_num)]
    rw [hgauge, hhiggs]
    have hset : ({GeneratorClass.gauge} ∪ {GeneratorClass.higgs} : Finset GeneratorClass)
        = {GeneratorClass.gauge, GeneratorClass.higgs} := by decide
    refine Submodule.mul_le.mpr fun x hx y hy => ?_
    have := h.mul_mem_sectorMassWeight hx hy
    rwa [hset] at this

/-- A product of a gauge-weight piece and a Higgs-weight piece lands in the mixed
  sector of the total weight. -/
lemma mul_le_sectorMassWeight_gauge_higgs {a b w : ℕ} {X Y : Submodule ℂ B}
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a + b = w)
    (hX : X ≤ h.isGaugeSector.massWeightSubmodule a)
    (hY : Y ≤ h.isHiggsSector.massWeightSubmodule b) :
    X * Y ≤ h.sectorMassWeight {GeneratorClass.gauge, GeneratorClass.higgs} w := by
  have hset : ({GeneratorClass.gauge} ∪ {GeneratorClass.higgs} : Finset GeneratorClass)
      = {GeneratorClass.gauge, GeneratorClass.higgs} := by decide
  refine Submodule.mul_le.mpr fun x hx y hy => ?_
  have hx' : x ∈ h.sectorMassWeight {GeneratorClass.gauge} a := by
    rw [h.sectorMassWeight_gauge_eq ha]; exact hX hx
  have hy' : y ∈ h.sectorMassWeight {GeneratorClass.higgs} b := by
    rw [h.sectorMassWeight_higgs_eq hb]; exact hY hy
  have hmem := h.mul_mem_sectorMassWeight hx' hy'
  rwa [hset, hab] at hmem

/-- **The mixed gauge-Higgs sector at weight `8`.** The surviving splittings are
  `4 + 4` and `6 + 2`, giving the field strength against the weight-four Higgs terms
  and the once-derived field strength against the underived Higgs. -/
lemma sectorMassWeight_gauge_higgs_eight :
    h.sectorMassWeight {GeneratorClass.gauge, GeneratorClass.higgs} 8
      = h.isGaugeSector.derivSubmodule 0 * h.isHiggsSector.derivSubmodule 1
        ⊔ h.isGaugeSector.derivSubmodule 0 * h.isHiggsSector.derivSubmodule 0
          * h.isHiggsSector.derivSubmodule 0
        ⊔ h.isGaugeSector.derivSubmodule 1 * h.isHiggsSector.derivSubmodule 0 := by
  refine le_antisymm ?_ ?_
  case refine_2 =>
    refine sup_le (sup_le ?_ ?_) ?_
    · exact h.mul_le_sectorMassWeight_gauge_higgs (a := 4) (b := 4) (by norm_num)
        (by norm_num) (by norm_num) (le_of_eq h.isGaugeSector.massWeightSubmodule_four_eq.symm)
        (by rw [h.isHiggsSector.massWeightSubmodule_four_eq_deriv]; exact le_sup_left)
    · rw [mul_assoc]
      exact h.mul_le_sectorMassWeight_gauge_higgs (a := 4) (b := 4) (by norm_num)
        (by norm_num) (by norm_num) (le_of_eq h.isGaugeSector.massWeightSubmodule_four_eq.symm)
        (by rw [h.isHiggsSector.massWeightSubmodule_four_eq_deriv]; exact le_sup_right)
    · exact h.mul_le_sectorMassWeight_gauge_higgs (a := 6) (b := 2) (by norm_num)
        (by norm_num) (by norm_num) (le_of_eq h.isGaugeSector.massWeightSubmodule_six_eq.symm)
        (le_of_eq h.isHiggsSector.massWeightSubmodule_two_eq_deriv.symm)
  rw [mul_assoc]
  have ho : ∀ k : ℕ, Odd k → h.isHiggsSector.massWeightSubmodule k = ⊥ :=
    fun k hk => h.isHiggsSector.massWeightSubmodule_odd_eq_bot k hk
  refine (h.sectorMassWeight_gauge_higgs_le 8).trans
    (iSup_le fun p => iSup_le fun hp => iSup_le fun h1 => iSup_le fun h2 => ?_)
  obtain ⟨a, b⟩ := p
  dsimp only at hp h1 h2 ⊢
  have ha : a ≤ 7 := by omega
  have hb : b ≤ 7 := by omega
  interval_cases a <;> interval_cases b <;>
    first
      | omega
      | simp [h.isGaugeSector.massWeightSubmodule_one_eq,
          h.isGaugeSector.massWeightSubmodule_two_eq,
          h.isGaugeSector.massWeightSubmodule_three_eq,
          h.isGaugeSector.massWeightSubmodule_four_eq,
          h.isGaugeSector.massWeightSubmodule_five_eq,
          h.isGaugeSector.massWeightSubmodule_six_eq,
          h.isGaugeSector.massWeightSubmodule_seven_eq,
          h.isHiggsSector.massWeightSubmodule_two_eq_deriv,
          h.isHiggsSector.massWeightSubmodule_four_eq_deriv, Submodule.mul_sup,
          ho 1 (by decide), ho 3 (by decide), ho 5 (by decide), ho 7 (by decide),
          bot_le]

end IsCovStandardModel

end StandardModel
