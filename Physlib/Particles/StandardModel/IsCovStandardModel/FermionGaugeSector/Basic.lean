/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.IsCovStandardModel.Sectors
/-!
# The mixed gauge-fermion sector

The field-strength towers are bosonic, so they commute with every fermion tower
(`h.F_comm_d`, `h.F_comm_bard`, ..., `h.F_comm_bare`); consequently the gauge algebra
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

/-!

## The gauge and fermion algebras commute

-/

/-- The gauge algebra and the fermion algebra commute element-wise: every generator of
  the gauge algebra commutes with every generator of the fermion algebra by the
  structure fields `h.F_comm_d`, ..., `h.F_comm_bare`, and commutation extends from
  generators to the algebras they generate. -/
lemma commute_of_mem_gaugeAlgebra_of_mem_fermionAlgebra {x y : B}
    (hx : x ∈ h.isGaugeSector.gaugeAlgebra) (hy : y ∈ h.isFermionSector.fermionAlgebra) :
    Commute x y := by
  have hgen : ∀ a ∈ (⋃ (n : ℕ) (l : Fin n → Fin 1 ⊕ Fin 3) (μ : Fin 1 ⊕ Fin 3)
        (ν : Fin 1 ⊕ Fin 3), Set.range (F l μ ν)),
      ∀ b ∈ (⋃ (i : Fin 3) (n : ℕ) (l : Fin n → Fin 1 ⊕ Fin 3),
        Set.range (d i l) ∪ Set.range (bard i l) ∪
        Set.range (u i l) ∪ Set.range (baru i l) ∪
        Set.range (Q i l) ∪ Set.range (barQ i l) ∪
        Set.range (L i l) ∪ Set.range (barL i l) ∪
        Set.range (e i l) ∪ Set.range (bare i l)), Commute a b := by
    intro a ha b hb
    simp only [Set.mem_iUnion, Set.mem_range] at ha
    obtain ⟨n, l, μ, ν, φ, rfl⟩ := ha
    simp only [Set.mem_iUnion, Set.mem_union, Set.mem_range] at hb
    obtain ⟨i, k, dd, (((((((((⟨φ', rfl⟩ | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) |
      ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩)⟩ := hb
    · exact h.F_comm_d l μ ν φ i dd φ'
    · exact h.F_comm_bard l μ ν φ i dd φ'
    · exact h.F_comm_u l μ ν φ i dd φ'
    · exact h.F_comm_baru l μ ν φ i dd φ'
    · exact h.F_comm_Q l μ ν φ i dd φ'
    · exact h.F_comm_barQ l μ ν φ i dd φ'
    · exact h.F_comm_L l μ ν φ i dd φ'
    · exact h.F_comm_barL l μ ν φ i dd φ'
    · exact h.F_comm_e l μ ν φ i dd φ'
    · exact h.F_comm_bare l μ ν φ i dd φ'
  rw [IsGaugeSector.gaugeAlgebra] at hx
  rw [IsFermionSector.fermionAlgebra] at hy
  refine Algebra.commute_of_mem_adjoin_of_forall_mem_commute hy fun b hb => ?_
  exact (Algebra.commute_of_mem_adjoin_of_forall_mem_commute hx
    fun a ha => (hgen a ha b hb).symm).symm

/-- The fermion sector's mass-weight submodules and the gauge sector's mass-weight
  submodules commute past each other, in the order needed by
  `sectorMassWeight_pair_le`. -/
lemma fermionMassWeight_mul_gaugeMassWeight_le (a b : ℕ) :
    h.isFermionSector.massWeightSubmodule a * h.isGaugeSector.massWeightSubmodule b
      ≤ h.isGaugeSector.massWeightSubmodule b * h.isFermionSector.massWeightSubmodule a := by
  refine Submodule.mul_le.mpr fun x hx y hy => ?_
  rw [(h.commute_of_mem_gaugeAlgebra_of_mem_fermionAlgebra
    (h.isGaugeSector.mem_gaugeAlgebra_of_mem_massWeightSubmodule hy)
    (h.isFermionSector.mem_fermionAlgebra_of_mem_massWeightSubmodule hx)).symm.eq]
  exact Submodule.mul_mem_mul hy hx

/-!

## The mixed gauge-fermion sector

-/

/-- **The mixed gauge-fermion sector decomposition.** The weight-`w` piece of the
  `{gauge, fermion}` sector lies in the join, over the splittings of `w` into two
  non-zero parts, of the products of the gauge and fermion sectors' own mass-weight
  submodules. -/
lemma sectorMassWeight_gauge_fermion_le (w : ℕ) :
    h.sectorMassWeight {GeneratorClass.gauge, GeneratorClass.fermion} w
      ≤ ⨆ (p : ℕ × ℕ) (_ : p.1 + p.2 = w) (_ : p.1 ≠ 0) (_ : p.2 ≠ 0),
        h.isGaugeSector.massWeightSubmodule p.1 * h.isFermionSector.massWeightSubmodule p.2 :=
  h.sectorMassWeight_pair_le (c₁ := GeneratorClass.gauge) (c₂ := GeneratorClass.fermion)
    (M₁ := h.isGaugeSector.massWeightSubmodule) (M₂ := h.isFermionSector.massWeightSubmodule)
    (by decide)
    (fun w => h.sectorMassWeight_gauge_le w) (fun w => h.sectorMassWeight_fermion_le w)
    h.isGaugeSector.one_le_massWeightSubmodule_zero
    h.isFermionSector.one_le_massWeightSubmodule_zero
    (fun a b => h.isGaugeSector.massWeightSubmodule_mul_le a b)
    (fun a b => h.isFermionSector.massWeightSubmodule_mul_le a b)
    (fun a b => h.fermionMassWeight_mul_gaugeMassWeight_le a b) w

/-- **The mixed gauge-fermion sector vanishes below weight `7`.** A non-zero gauge
  weight is at least `4` and a non-zero fermion weight is at least `3`, so no
  splitting of a weight below `7` into two non-zero parts can supply both. -/
lemma sectorMassWeight_gauge_fermion_eq_bot_of_lt_seven {w : ℕ} (hw : w < 7) :
    h.sectorMassWeight {GeneratorClass.gauge, GeneratorClass.fermion} w = ⊥ := by
  refine le_bot_iff.mp ((h.sectorMassWeight_gauge_fermion_le w).trans ?_)
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
          h.isFermionSector.massWeightSubmodule_one_eq,
          h.isFermionSector.massWeightSubmodule_two_eq,
          h.isFermionSector.massWeightSubmodule_four_eq]

/-- **The mixed gauge-fermion sector vanishes at weight `8`.** The only splittings of
  `8` into two non-zero parts with a non-zero gauge weight and a non-zero fermion
  weight would need the gauge part to be `4` or `6`(with fermion part `4` or `2`), but
  the fermion sector vanishes at both `4` and `2`. -/
lemma sectorMassWeight_gauge_fermion_eight :
    h.sectorMassWeight {GeneratorClass.gauge, GeneratorClass.fermion} 8 = ⊥ := by
  refine le_bot_iff.mp ((h.sectorMassWeight_gauge_fermion_le 8).trans ?_)
  refine iSup_le fun p => iSup_le fun hp => iSup_le fun h1 => iSup_le fun h2 => ?_
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
          h.isGaugeSector.massWeightSubmodule_five_eq,
          h.isGaugeSector.massWeightSubmodule_seven_eq,
          h.isFermionSector.massWeightSubmodule_one_eq,
          h.isFermionSector.massWeightSubmodule_two_eq,
          h.isFermionSector.massWeightSubmodule_four_eq]

/-- **The mixed gauge-fermion sector at weight `7`** is exactly the product of the
  underived field-strength submodule with the underived fermion submodule: the only
  splitting of `7` into a non-zero gauge weight and a non-zero fermion weight that
  survives is `4 + 3`. -/
lemma sectorMassWeight_gauge_fermion_seven :
    h.sectorMassWeight {GeneratorClass.gauge, GeneratorClass.fermion} 7
      = h.isGaugeSector.derivSubmodule 0 * h.isFermionSector.derivSubmodule 0 := by
  refine le_antisymm ?_ ?_
  · refine (h.sectorMassWeight_gauge_fermion_le 7).trans
      (iSup_le fun p => iSup_le fun hp => iSup_le fun h1 => iSup_le fun h2 => ?_)
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
            h.isGaugeSector.massWeightSubmodule_four_eq,
            h.isGaugeSector.massWeightSubmodule_five_eq,
            h.isGaugeSector.massWeightSubmodule_six_eq,
            h.isFermionSector.massWeightSubmodule_one_eq,
            h.isFermionSector.massWeightSubmodule_two_eq,
            h.isFermionSector.massWeightSubmodule_three_eq, bot_le]
  · have hgauge : h.isGaugeSector.derivSubmodule 0 = h.sectorMassWeight {GeneratorClass.gauge} 4 := by
      rw [← h.isGaugeSector.massWeightSubmodule_four_eq, ← h.sectorMassWeight_gauge_eq (by norm_num)]
    have hfermion : h.isFermionSector.derivSubmodule 0
        = h.sectorMassWeight {GeneratorClass.fermion} 3 := by
      rw [← h.isFermionSector.massWeightSubmodule_three_eq,
        ← h.sectorMassWeight_fermion_eq (by norm_num)]
    rw [hgauge, hfermion]
    have hset : ({GeneratorClass.gauge} ∪ {GeneratorClass.fermion} : Finset GeneratorClass)
        = {GeneratorClass.gauge, GeneratorClass.fermion} := by decide
    refine Submodule.mul_le.mpr fun x hx y hy => ?_
    have := h.mul_mem_sectorMassWeight hx hy
    rwa [hset] at this

end IsCovStandardModel

end StandardModel
