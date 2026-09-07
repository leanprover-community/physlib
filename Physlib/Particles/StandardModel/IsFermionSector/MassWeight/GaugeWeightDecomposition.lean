/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.IsFermionSector.MassWeight.Basic
public import Physlib.Particles.StandardModel.IsFermionSector.DerivSubmodule.GaugeWeightDecomposition
/-!
# The gauge weight decomposition of the fermion mass-weight submodules

Each mass-weight submodule of the fermion sector up to weight eight has an explicit
description in terms of the derivative submodules, and the derivative submodules carry
a gauge weight decomposition.  Transporting the latter along the former decomposes
every mass-weight submodule up to weight eight: weights one, two and four are trivial,
weights three, five and seven are the towers with zero, one and two covariant
derivatives, weight six is the product of two underived towers, and weight eight is the
kinetic sector.

-/

@[expose] public section

namespace StandardModel

open Matrix MatrixGroups

namespace IsFermionSector

variable {B : Type} [Ring B] [Algebra ℂ B]
  {repGauge : Representation ℂ GaugeGroupI B}
  {hrepGauge_mul : ∀ (g : GaugeGroupI) (b₁ b₂ : B),
    repGauge g (b₁ * b₂) = repGauge g b₁ * repGauge g b₂}
  {repLorentz : Representation ℂ SL(2,ℂ) B}
  {hrepLorentz_mul : ∀ (Λ : SL(2,ℂ)) (b₁ b₂ : B),
    repLorentz Λ (b₁ * b₂) = repLorentz Λ b₁ * repLorentz Λ b₂}
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
  {massWeightPoly : B →ₐ[ℂ] Polynomial B}
  (h : IsFermionSector B repGauge hrepGauge_mul repLorentz hrepLorentz_mul
      d bard u baru Q barQ L barL e bare massWeightPoly)

/-- Weight one is trivial. -/
@[implicit_reducible]
noncomputable def massWeightSubmoduleGaugeWeightOne :
    GaugeWeightDecomposition repGauge (h.massWeightSubmodule 1) :=
  GaugeWeightDecomposition.copy (GaugeWeightDecomposition.bot hrepGauge_mul) _
    h.massWeightSubmodule_one_eq

/-- Weight two is trivial. -/
@[implicit_reducible]
noncomputable def massWeightSubmoduleGaugeWeightTwo :
    GaugeWeightDecomposition repGauge (h.massWeightSubmodule 2) :=
  GaugeWeightDecomposition.copy (GaugeWeightDecomposition.bot hrepGauge_mul) _
    h.massWeightSubmodule_two_eq

/-- Weight three is the underived fermion towers. -/
@[implicit_reducible]
noncomputable def massWeightSubmoduleGaugeWeightThree :
    GaugeWeightDecomposition repGauge (h.massWeightSubmodule 3) :=
  GaugeWeightDecomposition.copy (h.derivSubmoduleGaugeWeight 0) _
    h.massWeightSubmodule_three_eq

/-- Weight four is trivial. -/
@[implicit_reducible]
noncomputable def massWeightSubmoduleGaugeWeightFour :
    GaugeWeightDecomposition repGauge (h.massWeightSubmodule 4) :=
  GaugeWeightDecomposition.copy (GaugeWeightDecomposition.bot hrepGauge_mul) _
    h.massWeightSubmodule_four_eq

/-- Weight five is the once-derived fermion towers. -/
@[implicit_reducible]
noncomputable def massWeightSubmoduleGaugeWeightFive :
    GaugeWeightDecomposition repGauge (h.massWeightSubmodule 5) :=
  GaugeWeightDecomposition.copy (h.derivSubmoduleGaugeWeight 1) _
    h.massWeightSubmodule_five_eq

/-- Weight six is the products of two underived fermion towers. -/
@[implicit_reducible]
noncomputable def massWeightSubmoduleGaugeWeightSix :
    GaugeWeightDecomposition repGauge (h.massWeightSubmodule 6) :=
  GaugeWeightDecomposition.copy (GaugeWeightDecomposition.mul (d := h.derivSubmoduleGaugeWeight 0)
      (d' := h.derivSubmoduleGaugeWeight 0)) _
    h.massWeightSubmodule_six_eq

/-- Weight seven is the twice-derived fermion towers. -/
@[implicit_reducible]
noncomputable def massWeightSubmoduleGaugeWeightSeven :
    GaugeWeightDecomposition repGauge (h.massWeightSubmodule 7) :=
  GaugeWeightDecomposition.copy (h.derivSubmoduleGaugeWeight 2) _
    h.massWeightSubmodule_seven_eq

/-- Weight eight is the kinetic sector: an underived tower against a once-derived one. -/
@[implicit_reducible]
noncomputable def massWeightSubmoduleGaugeWeightEight :
    GaugeWeightDecomposition repGauge (h.massWeightSubmodule 8) :=
  GaugeWeightDecomposition.copy (GaugeWeightDecomposition.mul (d := h.derivSubmoduleGaugeWeight 0)
      (d' := h.derivSubmoduleGaugeWeight 1)) _
    h.massWeightSubmodule_eight_eq

/-!

## The weight-zero pieces

-/

/-- Every gauge weight carried by a fermion symbol has nonzero hypercharge: each of the
  ten species has a fixed nonzero hypercharge, independent of colour, isospin and
  family, and the barred species carry the negative of the unbarred one. So the zero
  weight never occurs. -/
lemma zero_not_mem_fermionGaugeWeights : (0 : GaugeWeight) ∉ fermionGaugeWeights := by
  decide

/-- The weight-zero piece of the fermion derivative submodules is trivial: unlike
  the gauge sector, no single fermion symbol is a gauge singlet, since every one of the
  ten species carries a fixed nonzero hypercharge. A gauge-invariant combination needs
  at least two fermion insertions, which is why it is the mass weights six and eight,
  the products of two towers, that carry the interesting weight-zero content. -/
lemma derivSubmoduleGaugeWeight_piece_zero (n : ℕ) :
    (h.derivSubmoduleGaugeWeight n).piece 0 = ⊥ :=
  (h.derivSubmoduleGaugeWeight n).piece_eq_zero_of_not_mem_supp 0
    (h.derivSubmoduleGaugeWeight_supp n ▸ zero_not_mem_fermionGaugeWeights)

/-- The weight-zero piece at mass weight 1: the submodule itself is trivial. -/
lemma massWeightSubmoduleGaugeWeightOne_piece_zero :
    (h.massWeightSubmoduleGaugeWeightOne).piece 0 = ⊥ := rfl

/-- The weight-zero piece at mass weight 2: the submodule itself is trivial. -/
lemma massWeightSubmoduleGaugeWeightTwo_piece_zero :
    (h.massWeightSubmoduleGaugeWeightTwo).piece 0 = ⊥ := rfl

/-- The weight-zero piece at mass weight three: the underived fermion towers carry no
  gauge singlet, since every fermion symbol has nonzero hypercharge. -/
lemma massWeightSubmoduleGaugeWeightThree_piece_zero :
    (h.massWeightSubmoduleGaugeWeightThree).piece 0 = ⊥ :=
  h.derivSubmoduleGaugeWeight_piece_zero 0

/-- The weight-zero piece at mass weight 4: the submodule itself is trivial. -/
lemma massWeightSubmoduleGaugeWeightFour_piece_zero :
    (h.massWeightSubmoduleGaugeWeightFour).piece 0 = ⊥ := rfl

/-- The weight-zero piece at mass weight five: the once-derived fermion towers carry no
  gauge singlet, since every fermion symbol has nonzero hypercharge. -/
lemma massWeightSubmoduleGaugeWeightFive_piece_zero :
    (h.massWeightSubmoduleGaugeWeightFive).piece 0 = ⊥ :=
  h.derivSubmoduleGaugeWeight_piece_zero 1

/-- The weight-zero piece at mass weight seven: the twice-derived fermion towers carry
  no gauge singlet, since every fermion symbol has nonzero hypercharge. -/
lemma massWeightSubmoduleGaugeWeightSeven_piece_zero :
    (h.massWeightSubmoduleGaugeWeightSeven).piece 0 = ⊥ :=
  h.derivSubmoduleGaugeWeight_piece_zero 2

/-!

### Infrastructure for the product weights six and eight

Mass weights six and eight are products of two fermion towers, and their weight-zero
piece is genuinely nontrivial: it is spanned by pairing each species with its own
conjugate (a mass term). Splitting the product decomposition down to the ten species
and discarding the non-conjugate pairings, whose hypercharges never cancel, takes the
infrastructure developed here.

-/

/-- If the left factor of a product decomposition is a join `VA ⊔ VB`, its weight-`w`
  piece splits along the join. -/
lemma piece_sup_mul {VA VB VC : Submodule ℂ B}
    (dA : GaugeWeightDecomposition repGauge VA) (dB : GaugeWeightDecomposition repGauge VB)
    (dC : GaugeWeightDecomposition repGauge VC) (w : GaugeWeight) :
    (GaugeWeightDecomposition.mul (d := GaugeWeightDecomposition.sup (d := dA) (d' := dB))
        (d' := dC)).piece w
      = (GaugeWeightDecomposition.mul (d := dA) (d' := dC)).piece w
        ⊔ (GaugeWeightDecomposition.mul (d := dB) (d' := dC)).piece w :=
  GaugeWeightDecomposition.piece_congr
    (d := GaugeWeightDecomposition.mul (d := GaugeWeightDecomposition.sup (d := dA) (d' := dB))
      (d' := dC))
    (d' := GaugeWeightDecomposition.sup (d := GaugeWeightDecomposition.mul (d := dA) (d' := dC))
      (d' := GaugeWeightDecomposition.mul (d := dB) (d' := dC)))
    (Submodule.sup_mul VA VB VC) w

/-- If the right factor of a product decomposition is a join `VA ⊔ VB`, its weight-`w`
  piece splits along the join. -/
lemma piece_mul_sup {VA VB VC : Submodule ℂ B}
    (dC : GaugeWeightDecomposition repGauge VC) (dA : GaugeWeightDecomposition repGauge VA)
    (dB : GaugeWeightDecomposition repGauge VB) (w : GaugeWeight) :
    (GaugeWeightDecomposition.mul (d := dC)
        (d' := GaugeWeightDecomposition.sup (d := dA) (d' := dB))).piece w
      = (GaugeWeightDecomposition.mul (d := dC) (d' := dA)).piece w
        ⊔ (GaugeWeightDecomposition.mul (d := dC) (d' := dB)).piece w :=
  GaugeWeightDecomposition.piece_congr
    (d := GaugeWeightDecomposition.mul (d := dC)
      (d' := GaugeWeightDecomposition.sup (d := dA) (d' := dB)))
    (d' := GaugeWeightDecomposition.sup (d := GaugeWeightDecomposition.mul (d := dC) (d' := dA))
      (d' := GaugeWeightDecomposition.mul (d := dC) (d' := dB)))
    (Submodule.mul_sup VC VA VB) w

/-- Two decompositions with constant, non-cancelling hypercharge across their whole
  supports have a trivial product at weight zero: a weight from one can never cancel
  a weight from the other. -/
lemma mul_piece_zero_eq_bot_of_hypercharge {V V' : Submodule ℂ B}
    {dV : GaugeWeightDecomposition repGauge V} {dV' : GaugeWeightDecomposition repGauge V'}
    {hc hc' : ℤ} (hV : ∀ w ∈ dV.supp, w.2.2.2 = hc) (hV' : ∀ w ∈ dV'.supp, w.2.2.2 = hc')
    (hne : hc + hc' ≠ 0) :
    (GaugeWeightDecomposition.mul (d := dV) (d' := dV')).piece 0 = ⊥ := by
  rw [show (GaugeWeightDecomposition.mul (d := dV) (d' := dV')).piece 0
      = GaugeWeightDecomposition.piece repGauge (V * V') 0 from rfl,
    GaugeWeightDecomposition.mul_piece_eq_sub (d := dV) (d' := dV') 0]
  refine le_antisymm (iSup₂_le fun w1 hw1 => ?_) bot_le
  have h1 := hV w1 hw1
  have h2 : (0 : GaugeWeight) - w1 ∉ dV'.supp := by
    intro hmem
    have h2' := hV' _ hmem
    have e : ((0 : GaugeWeight) - w1).2.2.2 = -(w1.2.2.2) := by
      rw [zero_sub, ← GaugeWeight.coord_three, ← GaugeWeight.coord_three, GaugeWeight.coord_neg]
    rw [e, h1] at h2'
    omega
  rw [dV'.piece_eq_zero_of_not_mem_supp _ h2, Submodule.mul_bot]

/-- The `d` symbols carry hypercharge `2` (the negative of the down-singlet's `-2`),
  independent of colour and family. -/
lemma rangeGaugeWeight_d_hc {n : ℕ} (f : Fin 3) (l : Fin n → Fin 1 ⊕ Fin 3) :
    ∀ w ∈ (h.rangeGaugeWeight_d f l).supp, w.2.2.2 = 2 := by
  rw [h.rangeGaugeWeight_d_supp]
  rintro w hw
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at hw
  obtain ⟨j, rfl⟩ := hw
  simp [DownSinglet.valueGaugeWeight]

/-- The `bard` symbols carry hypercharge `-2`, independent of colour and family. -/
lemma rangeGaugeWeight_bard_hc {n : ℕ} (f : Fin 3) (l : Fin n → Fin 1 ⊕ Fin 3) :
    ∀ w ∈ (h.rangeGaugeWeight_bard f l).supp, w.2.2.2 = -2 := by
  rw [h.rangeGaugeWeight_bard_supp]
  rintro w hw
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at hw
  obtain ⟨j, rfl⟩ := hw
  simp [DownSinglet.valueGaugeWeight]

/-- The `u` symbols carry hypercharge `-4`, independent of colour and family. -/
lemma rangeGaugeWeight_u_hc {n : ℕ} (f : Fin 3) (l : Fin n → Fin 1 ⊕ Fin 3) :
    ∀ w ∈ (h.rangeGaugeWeight_u f l).supp, w.2.2.2 = -4 := by
  rw [h.rangeGaugeWeight_u_supp]
  rintro w hw
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at hw
  obtain ⟨j, rfl⟩ := hw
  simp [UpSinglet.valueGaugeWeight]

/-- The `baru` symbols carry hypercharge `4`, independent of colour and family. -/
lemma rangeGaugeWeight_baru_hc {n : ℕ} (f : Fin 3) (l : Fin n → Fin 1 ⊕ Fin 3) :
    ∀ w ∈ (h.rangeGaugeWeight_baru f l).supp, w.2.2.2 = 4 := by
  rw [h.rangeGaugeWeight_baru_supp]
  rintro w hw
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at hw
  obtain ⟨j, rfl⟩ := hw
  simp [UpSinglet.valueGaugeWeight]

/-- The `Q` symbols carry hypercharge `-1`, independent of colour, isospin and
  family. -/
lemma rangeGaugeWeight_Q_hc {n : ℕ} (f : Fin 3) (l : Fin n → Fin 1 ⊕ Fin 3) :
    ∀ w ∈ (h.rangeGaugeWeight_Q f l).supp, w.2.2.2 = -1 := by
  rw [h.rangeGaugeWeight_Q_supp]
  rintro w hw
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at hw
  obtain ⟨j, rfl⟩ := hw
  simp [QuarkDoublet.valueGaugeWeight]

/-- The `barQ` symbols carry hypercharge `1`, independent of colour, isospin and
  family. -/
lemma rangeGaugeWeight_barQ_hc {n : ℕ} (f : Fin 3) (l : Fin n → Fin 1 ⊕ Fin 3) :
    ∀ w ∈ (h.rangeGaugeWeight_barQ f l).supp, w.2.2.2 = 1 := by
  rw [h.rangeGaugeWeight_barQ_supp]
  rintro w hw
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at hw
  obtain ⟨j, rfl⟩ := hw
  simp [QuarkDoublet.valueGaugeWeight]

/-- The `L` symbols carry hypercharge `3`, independent of isospin and family. -/
lemma rangeGaugeWeight_L_hc {n : ℕ} (f : Fin 3) (l : Fin n → Fin 1 ⊕ Fin 3) :
    ∀ w ∈ (h.rangeGaugeWeight_L f l).supp, w.2.2.2 = 3 := by
  rw [h.rangeGaugeWeight_L_supp]
  rintro w hw
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at hw
  obtain ⟨j, rfl⟩ := hw
  simp [LeptonDoublet.valueGaugeWeight]

/-- The `barL` symbols carry hypercharge `-3`, independent of isospin and family. -/
lemma rangeGaugeWeight_barL_hc {n : ℕ} (f : Fin 3) (l : Fin n → Fin 1 ⊕ Fin 3) :
    ∀ w ∈ (h.rangeGaugeWeight_barL f l).supp, w.2.2.2 = -3 := by
  rw [h.rangeGaugeWeight_barL_supp]
  rintro w hw
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at hw
  obtain ⟨j, rfl⟩ := hw
  simp [LeptonDoublet.valueGaugeWeight]

/-- The `e` symbols carry hypercharge `6`, independent of family. -/
lemma rangeGaugeWeight_e_hc {n : ℕ} (f : Fin 3) (l : Fin n → Fin 1 ⊕ Fin 3) :
    ∀ w ∈ (h.rangeGaugeWeight_e f l).supp, w.2.2.2 = 6 := by
  rw [h.rangeGaugeWeight_e_supp]
  rintro w hw
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at hw
  obtain ⟨j, rfl⟩ := hw
  simp [LeptonSinglet.valueGaugeWeight]

/-- The `bare` symbols carry hypercharge `-6`, independent of family. -/
lemma rangeGaugeWeight_bare_hc {n : ℕ} (f : Fin 3) (l : Fin n → Fin 1 ⊕ Fin 3) :
    ∀ w ∈ (h.rangeGaugeWeight_bare f l).supp, w.2.2.2 = -6 := by
  rw [h.rangeGaugeWeight_bare_supp]
  rintro w hw
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at hw
  obtain ⟨j, rfl⟩ := hw
  simp [LeptonSinglet.valueGaugeWeight]

/-- The gauge weight decomposition of one family's full set of symbols at fixed
  derivative slots, matching the recipe of `derivSubmodule` itself: the join of the
  ten species' ranges. -/
@[implicit_reducible]
noncomputable def speciesGaugeWeight (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) :
    GaugeWeightDecomposition repGauge
      (LinearMap.range (d f l) ⊔ LinearMap.range (bard f l) ⊔
        LinearMap.range (u f l) ⊔ LinearMap.range (baru f l) ⊔
        LinearMap.range (Q f l) ⊔ LinearMap.range (barQ f l) ⊔
        LinearMap.range (L f l) ⊔ LinearMap.range (barL f l) ⊔
        LinearMap.range (e f l) ⊔ LinearMap.range (bare f l)) :=
  GaugeWeightDecomposition.sup (d := GaugeWeightDecomposition.sup
  (d := GaugeWeightDecomposition.sup
  (d := GaugeWeightDecomposition.sup
  (d := GaugeWeightDecomposition.sup
  (d := GaugeWeightDecomposition.sup
  (d := GaugeWeightDecomposition.sup
  (d := GaugeWeightDecomposition.sup
  (d := GaugeWeightDecomposition.sup
  (d := h.rangeGaugeWeight_d f l)
  (d' := h.rangeGaugeWeight_bard f l))
  (d' := h.rangeGaugeWeight_u f l))
  (d' := h.rangeGaugeWeight_baru f l))
  (d' := h.rangeGaugeWeight_Q f l))
  (d' := h.rangeGaugeWeight_barQ f l))
  (d' := h.rangeGaugeWeight_L f l))
  (d' := h.rangeGaugeWeight_barL f l))
  (d' := h.rangeGaugeWeight_e f l))
  (d' := h.rangeGaugeWeight_bare f l)

/-- The weight-zero piece of the product of two families' full symbol sets collapses
  to the ten conjugate pairings: every other combination of species has hypercharges
  that cannot cancel. -/
lemma speciesGaugeWeight_mul_piece_zero {n m : ℕ} (f f' : Fin 3) (l : Fin n → Fin 1 ⊕ Fin 3)
    (l' : Fin m → Fin 1 ⊕ Fin 3) :
    (GaugeWeightDecomposition.mul (d := h.speciesGaugeWeight f l)
        (d' := h.speciesGaugeWeight f' l')).piece 0
      =
      (GaugeWeightDecomposition.mul (d := h.rangeGaugeWeight_d f l)
            (d' := h.rangeGaugeWeight_bard f' l')).piece 0
        ⊔ (GaugeWeightDecomposition.mul (d := h.rangeGaugeWeight_bard f l)
            (d' := h.rangeGaugeWeight_d f' l')).piece 0
        ⊔ (GaugeWeightDecomposition.mul (d := h.rangeGaugeWeight_u f l)
            (d' := h.rangeGaugeWeight_baru f' l')).piece 0
        ⊔ (GaugeWeightDecomposition.mul (d := h.rangeGaugeWeight_baru f l)
            (d' := h.rangeGaugeWeight_u f' l')).piece 0
        ⊔ (GaugeWeightDecomposition.mul (d := h.rangeGaugeWeight_Q f l)
            (d' := h.rangeGaugeWeight_barQ f' l')).piece 0
        ⊔ (GaugeWeightDecomposition.mul (d := h.rangeGaugeWeight_barQ f l)
            (d' := h.rangeGaugeWeight_Q f' l')).piece 0
        ⊔ (GaugeWeightDecomposition.mul (d := h.rangeGaugeWeight_L f l)
            (d' := h.rangeGaugeWeight_barL f' l')).piece 0
        ⊔ (GaugeWeightDecomposition.mul (d := h.rangeGaugeWeight_barL f l)
            (d' := h.rangeGaugeWeight_L f' l')).piece 0
        ⊔ (GaugeWeightDecomposition.mul (d := h.rangeGaugeWeight_e f l)
            (d' := h.rangeGaugeWeight_bare f' l')).piece 0
        ⊔ (GaugeWeightDecomposition.mul (d := h.rangeGaugeWeight_bare f l)
            (d' := h.rangeGaugeWeight_e f' l')).piece 0 := by
  simp only [piece_sup_mul, piece_mul_sup,
    mul_piece_zero_eq_bot_of_hypercharge (h.rangeGaugeWeight_d_hc f l)
      (h.rangeGaugeWeight_d_hc f' l') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge (h.rangeGaugeWeight_d_hc f l)
      (h.rangeGaugeWeight_u_hc f' l') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge (h.rangeGaugeWeight_d_hc f l)
      (h.rangeGaugeWeight_baru_hc f' l') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge (h.rangeGaugeWeight_d_hc f l)
      (h.rangeGaugeWeight_Q_hc f' l') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge (h.rangeGaugeWeight_d_hc f l)
      (h.rangeGaugeWeight_barQ_hc f' l') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge (h.rangeGaugeWeight_d_hc f l)
      (h.rangeGaugeWeight_L_hc f' l') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge (h.rangeGaugeWeight_d_hc f l)
      (h.rangeGaugeWeight_barL_hc f' l') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge (h.rangeGaugeWeight_d_hc f l)
      (h.rangeGaugeWeight_e_hc f' l') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge (h.rangeGaugeWeight_d_hc f l)
      (h.rangeGaugeWeight_bare_hc f' l') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge (h.rangeGaugeWeight_bard_hc f l)
      (h.rangeGaugeWeight_bard_hc f' l') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge (h.rangeGaugeWeight_bard_hc f l)
      (h.rangeGaugeWeight_u_hc f' l') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge (h.rangeGaugeWeight_bard_hc f l)
      (h.rangeGaugeWeight_baru_hc f' l') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge (h.rangeGaugeWeight_bard_hc f l)
      (h.rangeGaugeWeight_Q_hc f' l') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge (h.rangeGaugeWeight_bard_hc f l)
      (h.rangeGaugeWeight_barQ_hc f' l') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge (h.rangeGaugeWeight_bard_hc f l)
      (h.rangeGaugeWeight_L_hc f' l') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge (h.rangeGaugeWeight_bard_hc f l)
      (h.rangeGaugeWeight_barL_hc f' l') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge (h.rangeGaugeWeight_bard_hc f l)
      (h.rangeGaugeWeight_e_hc f' l') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge (h.rangeGaugeWeight_bard_hc f l)
      (h.rangeGaugeWeight_bare_hc f' l') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge (h.rangeGaugeWeight_u_hc f l)
      (h.rangeGaugeWeight_d_hc f' l') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge (h.rangeGaugeWeight_u_hc f l)
      (h.rangeGaugeWeight_bard_hc f' l') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge (h.rangeGaugeWeight_u_hc f l)
      (h.rangeGaugeWeight_u_hc f' l') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge (h.rangeGaugeWeight_u_hc f l)
      (h.rangeGaugeWeight_Q_hc f' l') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge (h.rangeGaugeWeight_u_hc f l)
      (h.rangeGaugeWeight_barQ_hc f' l') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge (h.rangeGaugeWeight_u_hc f l)
      (h.rangeGaugeWeight_L_hc f' l') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge (h.rangeGaugeWeight_u_hc f l)
      (h.rangeGaugeWeight_barL_hc f' l') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge (h.rangeGaugeWeight_u_hc f l)
      (h.rangeGaugeWeight_e_hc f' l') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge (h.rangeGaugeWeight_u_hc f l)
      (h.rangeGaugeWeight_bare_hc f' l') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge (h.rangeGaugeWeight_baru_hc f l)
      (h.rangeGaugeWeight_d_hc f' l') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge (h.rangeGaugeWeight_baru_hc f l)
      (h.rangeGaugeWeight_bard_hc f' l') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge (h.rangeGaugeWeight_baru_hc f l)
      (h.rangeGaugeWeight_baru_hc f' l') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge (h.rangeGaugeWeight_baru_hc f l)
      (h.rangeGaugeWeight_Q_hc f' l') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge (h.rangeGaugeWeight_baru_hc f l)
      (h.rangeGaugeWeight_barQ_hc f' l') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge (h.rangeGaugeWeight_baru_hc f l)
      (h.rangeGaugeWeight_L_hc f' l') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge (h.rangeGaugeWeight_baru_hc f l)
      (h.rangeGaugeWeight_barL_hc f' l') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge (h.rangeGaugeWeight_baru_hc f l)
      (h.rangeGaugeWeight_e_hc f' l') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge (h.rangeGaugeWeight_baru_hc f l)
      (h.rangeGaugeWeight_bare_hc f' l') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge (h.rangeGaugeWeight_Q_hc f l)
      (h.rangeGaugeWeight_d_hc f' l') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge (h.rangeGaugeWeight_Q_hc f l)
      (h.rangeGaugeWeight_bard_hc f' l') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge (h.rangeGaugeWeight_Q_hc f l)
      (h.rangeGaugeWeight_u_hc f' l') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge (h.rangeGaugeWeight_Q_hc f l)
      (h.rangeGaugeWeight_baru_hc f' l') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge (h.rangeGaugeWeight_Q_hc f l)
      (h.rangeGaugeWeight_Q_hc f' l') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge (h.rangeGaugeWeight_Q_hc f l)
      (h.rangeGaugeWeight_L_hc f' l') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge (h.rangeGaugeWeight_Q_hc f l)
      (h.rangeGaugeWeight_barL_hc f' l') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge (h.rangeGaugeWeight_Q_hc f l)
      (h.rangeGaugeWeight_e_hc f' l') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge (h.rangeGaugeWeight_Q_hc f l)
      (h.rangeGaugeWeight_bare_hc f' l') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge (h.rangeGaugeWeight_barQ_hc f l)
      (h.rangeGaugeWeight_d_hc f' l') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge (h.rangeGaugeWeight_barQ_hc f l)
      (h.rangeGaugeWeight_bard_hc f' l') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge (h.rangeGaugeWeight_barQ_hc f l)
      (h.rangeGaugeWeight_u_hc f' l') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge (h.rangeGaugeWeight_barQ_hc f l)
      (h.rangeGaugeWeight_baru_hc f' l') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge (h.rangeGaugeWeight_barQ_hc f l)
      (h.rangeGaugeWeight_barQ_hc f' l') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge (h.rangeGaugeWeight_barQ_hc f l)
      (h.rangeGaugeWeight_L_hc f' l') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge (h.rangeGaugeWeight_barQ_hc f l)
      (h.rangeGaugeWeight_barL_hc f' l') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge (h.rangeGaugeWeight_barQ_hc f l)
      (h.rangeGaugeWeight_e_hc f' l') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge (h.rangeGaugeWeight_barQ_hc f l)
      (h.rangeGaugeWeight_bare_hc f' l') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge (h.rangeGaugeWeight_L_hc f l)
      (h.rangeGaugeWeight_d_hc f' l') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge (h.rangeGaugeWeight_L_hc f l)
      (h.rangeGaugeWeight_bard_hc f' l') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge (h.rangeGaugeWeight_L_hc f l)
      (h.rangeGaugeWeight_u_hc f' l') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge (h.rangeGaugeWeight_L_hc f l)
      (h.rangeGaugeWeight_baru_hc f' l') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge (h.rangeGaugeWeight_L_hc f l)
      (h.rangeGaugeWeight_Q_hc f' l') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge (h.rangeGaugeWeight_L_hc f l)
      (h.rangeGaugeWeight_barQ_hc f' l') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge (h.rangeGaugeWeight_L_hc f l)
      (h.rangeGaugeWeight_L_hc f' l') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge (h.rangeGaugeWeight_L_hc f l)
      (h.rangeGaugeWeight_e_hc f' l') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge (h.rangeGaugeWeight_L_hc f l)
      (h.rangeGaugeWeight_bare_hc f' l') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge (h.rangeGaugeWeight_barL_hc f l)
      (h.rangeGaugeWeight_d_hc f' l') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge (h.rangeGaugeWeight_barL_hc f l)
      (h.rangeGaugeWeight_bard_hc f' l') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge (h.rangeGaugeWeight_barL_hc f l)
      (h.rangeGaugeWeight_u_hc f' l') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge (h.rangeGaugeWeight_barL_hc f l)
      (h.rangeGaugeWeight_baru_hc f' l') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge (h.rangeGaugeWeight_barL_hc f l)
      (h.rangeGaugeWeight_Q_hc f' l') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge (h.rangeGaugeWeight_barL_hc f l)
      (h.rangeGaugeWeight_barQ_hc f' l') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge (h.rangeGaugeWeight_barL_hc f l)
      (h.rangeGaugeWeight_barL_hc f' l') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge (h.rangeGaugeWeight_barL_hc f l)
      (h.rangeGaugeWeight_e_hc f' l') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge (h.rangeGaugeWeight_barL_hc f l)
      (h.rangeGaugeWeight_bare_hc f' l') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge (h.rangeGaugeWeight_e_hc f l)
      (h.rangeGaugeWeight_d_hc f' l') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge (h.rangeGaugeWeight_e_hc f l)
      (h.rangeGaugeWeight_bard_hc f' l') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge (h.rangeGaugeWeight_e_hc f l)
      (h.rangeGaugeWeight_u_hc f' l') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge (h.rangeGaugeWeight_e_hc f l)
      (h.rangeGaugeWeight_baru_hc f' l') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge (h.rangeGaugeWeight_e_hc f l)
      (h.rangeGaugeWeight_Q_hc f' l') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge (h.rangeGaugeWeight_e_hc f l)
      (h.rangeGaugeWeight_barQ_hc f' l') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge (h.rangeGaugeWeight_e_hc f l)
      (h.rangeGaugeWeight_L_hc f' l') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge (h.rangeGaugeWeight_e_hc f l)
      (h.rangeGaugeWeight_barL_hc f' l') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge (h.rangeGaugeWeight_e_hc f l)
      (h.rangeGaugeWeight_e_hc f' l') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge (h.rangeGaugeWeight_bare_hc f l)
      (h.rangeGaugeWeight_d_hc f' l') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge (h.rangeGaugeWeight_bare_hc f l)
      (h.rangeGaugeWeight_bard_hc f' l') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge (h.rangeGaugeWeight_bare_hc f l)
      (h.rangeGaugeWeight_u_hc f' l') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge (h.rangeGaugeWeight_bare_hc f l)
      (h.rangeGaugeWeight_baru_hc f' l') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge (h.rangeGaugeWeight_bare_hc f l)
      (h.rangeGaugeWeight_Q_hc f' l') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge (h.rangeGaugeWeight_bare_hc f l)
      (h.rangeGaugeWeight_barQ_hc f' l') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge (h.rangeGaugeWeight_bare_hc f l)
      (h.rangeGaugeWeight_L_hc f' l') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge (h.rangeGaugeWeight_bare_hc f l)
      (h.rangeGaugeWeight_barL_hc f' l') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge (h.rangeGaugeWeight_bare_hc f l)
      (h.rangeGaugeWeight_bare_hc f' l') (by decide),
    bot_sup_eq, sup_bot_eq]
  ac_rfl

/-- The zero-index derivative slot collapses a supremum over it to its value: there
  is nothing to derive with respect to. -/
lemma iSup_fin_zero_eq {α : Type} [CompleteLattice α] (F : (Fin 0 → Fin 1 ⊕ Fin 3) → α) :
    ⨆ l, F l = F ![] :=
  le_antisymm (iSup_le fun l => by rw [Subsingleton.elim l ![]]) (le_iSup F ![])

/-- The underived derivative submodule as a join over families alone, the trivial
  derivative slot dropped. -/
lemma derivSubmodule_zero_eq :
    h.derivSubmodule 0 = ⨆ (f : Fin 3),
      (LinearMap.range (d f ![]) ⊔
        LinearMap.range (bard f ![]) ⊔
        LinearMap.range (u f ![]) ⊔
        LinearMap.range (baru f ![]) ⊔
        LinearMap.range (Q f ![]) ⊔
        LinearMap.range (barQ f ![]) ⊔
        LinearMap.range (L f ![]) ⊔
        LinearMap.range (barL f ![]) ⊔
        LinearMap.range (e f ![]) ⊔
        LinearMap.range (bare f ![])) := by
  show (⨆ (_ : Fin 3) (_ : Fin 0 → Fin 1 ⊕ Fin 3), _) = _
  exact iSup_congr fun f => iSup_fin_zero_eq _

/-- The weight-zero piece at mass weight six, written out in the mass terms
  themselves: the join, over pairs of families, of the ten ways to pair each
  species with its own conjugate. Every other pairing of species has hypercharges
  that cannot cancel, by `speciesGaugeWeight_mul_piece_zero`. -/
lemma massWeightSubmoduleGaugeWeightSix_piece_zero :
    (h.massWeightSubmoduleGaugeWeightSix).piece 0
      = ⨆ (f : Fin 3) (f' : Fin 3),
        (GaugeWeightDecomposition.mul (d := h.rangeGaugeWeight_d f ![])
              (d' := h.rangeGaugeWeight_bard f' ![])).piece 0
          ⊔ (GaugeWeightDecomposition.mul (d := h.rangeGaugeWeight_bard f ![])
              (d' := h.rangeGaugeWeight_d f' ![])).piece 0
          ⊔ (GaugeWeightDecomposition.mul (d := h.rangeGaugeWeight_u f ![])
              (d' := h.rangeGaugeWeight_baru f' ![])).piece 0
          ⊔ (GaugeWeightDecomposition.mul (d := h.rangeGaugeWeight_baru f ![])
              (d' := h.rangeGaugeWeight_u f' ![])).piece 0
          ⊔ (GaugeWeightDecomposition.mul (d := h.rangeGaugeWeight_Q f ![])
              (d' := h.rangeGaugeWeight_barQ f' ![])).piece 0
          ⊔ (GaugeWeightDecomposition.mul (d := h.rangeGaugeWeight_barQ f ![])
              (d' := h.rangeGaugeWeight_Q f' ![])).piece 0
          ⊔ (GaugeWeightDecomposition.mul (d := h.rangeGaugeWeight_L f ![])
              (d' := h.rangeGaugeWeight_barL f' ![])).piece 0
          ⊔ (GaugeWeightDecomposition.mul (d := h.rangeGaugeWeight_barL f ![])
              (d' := h.rangeGaugeWeight_L f' ![])).piece 0
          ⊔ (GaugeWeightDecomposition.mul (d := h.rangeGaugeWeight_e f ![])
              (d' := h.rangeGaugeWeight_bare f' ![])).piece 0
          ⊔ (GaugeWeightDecomposition.mul (d := h.rangeGaugeWeight_bare f ![])
              (d' := h.rangeGaugeWeight_e f' ![])).piece 0 := by
  have hprod : h.derivSubmodule 0 * h.derivSubmodule 0
      = ⨆ (f : Fin 3) (f' : Fin 3),
        (LinearMap.range (d f ![]) ⊔
        LinearMap.range (bard f ![]) ⊔
        LinearMap.range (u f ![]) ⊔
        LinearMap.range (baru f ![]) ⊔
        LinearMap.range (Q f ![]) ⊔
        LinearMap.range (barQ f ![]) ⊔
        LinearMap.range (L f ![]) ⊔
        LinearMap.range (barL f ![]) ⊔
        LinearMap.range (e f ![]) ⊔
        LinearMap.range (bare f ![]))
          * (LinearMap.range (d f' ![]) ⊔
        LinearMap.range (bard f' ![]) ⊔
        LinearMap.range (u f' ![]) ⊔
        LinearMap.range (baru f' ![]) ⊔
        LinearMap.range (Q f' ![]) ⊔
        LinearMap.range (barQ f' ![]) ⊔
        LinearMap.range (L f' ![]) ⊔
        LinearMap.range (barL f' ![]) ⊔
        LinearMap.range (e f' ![]) ⊔
        LinearMap.range (bare f' ![])) := by
    rw [h.derivSubmodule_zero_eq, Submodule.iSup_mul]
    exact iSup_congr fun f => Submodule.mul_iSup _ _
  show (GaugeWeightDecomposition.mul (d := h.derivSubmoduleGaugeWeight 0)
      (d' := h.derivSubmoduleGaugeWeight 0)).piece 0 = _
  rw [GaugeWeightDecomposition.piece_congr
      (d := GaugeWeightDecomposition.mul (d := h.derivSubmoduleGaugeWeight 0)
        (d' := h.derivSubmoduleGaugeWeight 0))
      (d' := GaugeWeightDecomposition.iSup hrepGauge_mul (fun f =>
        GaugeWeightDecomposition.iSup hrepGauge_mul (fun f' =>
          GaugeWeightDecomposition.mul (d := h.speciesGaugeWeight f ![])
            (d' := h.speciesGaugeWeight f' ![]))))
      hprod 0]
  simp only [GaugeWeightDecomposition.piece_iSup]
  exact iSup_congr fun f => iSup_congr fun f' =>
    h.speciesGaugeWeight_mul_piece_zero f f' ![] ![]

/-- The weight-zero piece at mass weight eight, written out in the kinetic terms
  themselves: the join, over pairs of families and a once-derived slot, of the ten
  ways to pair each species with its own conjugate. Every other pairing of species has
  hypercharges that cannot cancel, by `speciesGaugeWeight_mul_piece_zero`. -/
lemma massWeightSubmoduleGaugeWeightEight_piece_zero :
    (h.massWeightSubmoduleGaugeWeightEight).piece 0
      = ⨆ (f : Fin 3) (f' : Fin 3) (l' : Fin 1 → Fin 1 ⊕ Fin 3),
        (GaugeWeightDecomposition.mul (d := h.rangeGaugeWeight_d f ![])
              (d' := h.rangeGaugeWeight_bard f' l')).piece 0
          ⊔ (GaugeWeightDecomposition.mul (d := h.rangeGaugeWeight_bard f ![])
              (d' := h.rangeGaugeWeight_d f' l')).piece 0
          ⊔ (GaugeWeightDecomposition.mul (d := h.rangeGaugeWeight_u f ![])
              (d' := h.rangeGaugeWeight_baru f' l')).piece 0
          ⊔ (GaugeWeightDecomposition.mul (d := h.rangeGaugeWeight_baru f ![])
              (d' := h.rangeGaugeWeight_u f' l')).piece 0
          ⊔ (GaugeWeightDecomposition.mul (d := h.rangeGaugeWeight_Q f ![])
              (d' := h.rangeGaugeWeight_barQ f' l')).piece 0
          ⊔ (GaugeWeightDecomposition.mul (d := h.rangeGaugeWeight_barQ f ![])
              (d' := h.rangeGaugeWeight_Q f' l')).piece 0
          ⊔ (GaugeWeightDecomposition.mul (d := h.rangeGaugeWeight_L f ![])
              (d' := h.rangeGaugeWeight_barL f' l')).piece 0
          ⊔ (GaugeWeightDecomposition.mul (d := h.rangeGaugeWeight_barL f ![])
              (d' := h.rangeGaugeWeight_L f' l')).piece 0
          ⊔ (GaugeWeightDecomposition.mul (d := h.rangeGaugeWeight_e f ![])
              (d' := h.rangeGaugeWeight_bare f' l')).piece 0
          ⊔ (GaugeWeightDecomposition.mul (d := h.rangeGaugeWeight_bare f ![])
              (d' := h.rangeGaugeWeight_e f' l')).piece 0 := by
  have hprod : h.derivSubmodule 0 * h.derivSubmodule 1
      = ⨆ (f : Fin 3) (f' : Fin 3) (l' : Fin 1 → Fin 1 ⊕ Fin 3),
        (LinearMap.range (d f ![]) ⊔
        LinearMap.range (bard f ![]) ⊔
        LinearMap.range (u f ![]) ⊔
        LinearMap.range (baru f ![]) ⊔
        LinearMap.range (Q f ![]) ⊔
        LinearMap.range (barQ f ![]) ⊔
        LinearMap.range (L f ![]) ⊔
        LinearMap.range (barL f ![]) ⊔
        LinearMap.range (e f ![]) ⊔
        LinearMap.range (bare f ![]))
          * (LinearMap.range (d f' l') ⊔
        LinearMap.range (bard f' l') ⊔
        LinearMap.range (u f' l') ⊔
        LinearMap.range (baru f' l') ⊔
        LinearMap.range (Q f' l') ⊔
        LinearMap.range (barQ f' l') ⊔
        LinearMap.range (L f' l') ⊔
        LinearMap.range (barL f' l') ⊔
        LinearMap.range (e f' l') ⊔
        LinearMap.range (bare f' l')) := by
    rw [h.derivSubmodule_zero_eq,
      show h.derivSubmodule 1 = ⨆ (f' : Fin 3) (l' : Fin 1 → Fin 1 ⊕ Fin 3),
        (LinearMap.range (d f' l') ⊔
        LinearMap.range (bard f' l') ⊔
        LinearMap.range (u f' l') ⊔
        LinearMap.range (baru f' l') ⊔
        LinearMap.range (Q f' l') ⊔
        LinearMap.range (barQ f' l') ⊔
        LinearMap.range (L f' l') ⊔
        LinearMap.range (barL f' l') ⊔
        LinearMap.range (e f' l') ⊔
        LinearMap.range (bare f' l')) from rfl,
      Submodule.iSup_mul]
    exact iSup_congr fun f => by
      rw [Submodule.mul_iSup]
      exact iSup_congr fun f' => Submodule.mul_iSup _ _
  show (GaugeWeightDecomposition.mul (d := h.derivSubmoduleGaugeWeight 0)
      (d' := h.derivSubmoduleGaugeWeight 1)).piece 0 = _
  rw [GaugeWeightDecomposition.piece_congr
      (d := GaugeWeightDecomposition.mul (d := h.derivSubmoduleGaugeWeight 0)
        (d' := h.derivSubmoduleGaugeWeight 1))
      (d' := GaugeWeightDecomposition.iSup hrepGauge_mul (fun f =>
        GaugeWeightDecomposition.iSup hrepGauge_mul (fun f' =>
          GaugeWeightDecomposition.iSup hrepGauge_mul (fun l' =>
            GaugeWeightDecomposition.mul (d := h.speciesGaugeWeight f ![])
              (d' := h.speciesGaugeWeight f' l')))))
      hprod 0]
  simp only [GaugeWeightDecomposition.piece_iSup]
  exact iSup_congr fun f => iSup_congr fun f' => iSup_congr fun l' =>
    h.speciesGaugeWeight_mul_piece_zero f f' ![] l'

/-!

## Invariants modulo a gauge-stable submodule

A submodule `S` closed under the gauge action can be discarded from a gauge-invariant
element: if `x` is gauge invariant and lies in a fermionic submodule joined with `S`, then
its fermionic part has to vanish and `x` already lies in `S`. The reason is the one behind
`derivSubmoduleGaugeWeight_piece_zero`: every one of the ten species carries a fixed nonzero
hypercharge, so no nonzero fermionic element is a gauge singlet.

The argument runs one weight at a time. Split off a piece of weight `w`, so that `x = a + y`
with `a` of pure weight `w` and `y` in the join of the remaining pieces with `S`. The
hypercharge generator `g` fixes `x` and scales `a` by some `c ≠ 1`, so
`(c - 1) • x = c • y - g y`, which lies in that smaller join because both the pieces and `S`
are stable under `g`. Dividing by `c - 1` deletes the weight `w`, and the induction closes on
the empty support. Only the hypercharge generator is needed, since it alone separates every
fermion weight from zero.

This is the fermionic analogue of `exists_smul_contraction_of_invariant_subset` for the
Lorentz group.

-/

/-- The one-weight-at-a-time refinement. Let `S` be closed under the gauge action and let `s`
  be a finite set of gauge weights each of which is seen by the `i`-th torus generator, in
  the sense that its `i`-th coordinate is nonzero. Then a gauge-invariant element of the join
  of the weight-`w` pieces for `w ∈ s` with `S` already lies in `S`. -/
lemma mem_of_invariant_of_mem_biSup_piece_sup {V S : Submodule ℂ B}
    (dV : GaugeWeightDecomposition repGauge V)
    (hS : ∀ (g : GaugeGroupI) (y : B), y ∈ S → repGauge g y ∈ S) (i : Fin 4) :
    ∀ (s : Finset GaugeWeight), (∀ w ∈ s, w.coord i ≠ 0) →
      ∀ x ∈ (⨆ w ∈ s, dV.piece w) ⊔ S, (∀ g : GaugeGroupI, repGauge g x = x) → x ∈ S := by
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro _ x hx _
    simpa using hx
  | @insert w₀ s' hw₀ ih =>
    intro hs x hx hinv
    rw [Finset.iSup_insert, sup_assoc] at hx
    obtain ⟨a, ha, y, hy, rfl⟩ := Submodule.mem_sup.mp hx
    have hc1 : ((expI : ℂ) ^ w₀.coord i) ≠ 1 := by
      intro hcc
      exact hs w₀ (Finset.mem_insert_self w₀ s')
        (expI_zpow_injective (show (expI : ℂ) ^ w₀.coord i = (expI : ℂ) ^ (0 : ℤ) by
          rw [zpow_zero]; exact hcc))
    have hpiece : ∀ w, ∀ z ∈ dV.piece w, repGauge (gaugeTorusGen i) z ∈ dV.piece w := by
      intro w z hz
      rw [dV.piece_le w z hz i]
      exact (dV.piece w).smul_mem _ hz
    have hmap : Submodule.map (repGauge (gaugeTorusGen i)) ((⨆ w ∈ s', dV.piece w) ⊔ S)
        ≤ (⨆ w ∈ s', dV.piece w) ⊔ S := by
      rw [Submodule.map_sup]
      refine sup_le (le_sup_of_le_left ?_) (le_sup_of_le_right ?_)
      · simp only [Submodule.map_iSup]
        exact iSup₂_le fun w hw => le_iSup₂_of_le w hw
          (Submodule.map_le_iff_le_comap.mpr fun z hz => hpiece w z hz)
      · exact Submodule.map_le_iff_le_comap.mpr fun z hz => hS _ z hz
    have hsum : ((expI : ℂ) ^ w₀.coord i) • a + repGauge (gaugeTorusGen i) y = a + y := by
      have hg := hinv (gaugeTorusGen i)
      rwa [map_add, dV.piece_le w₀ a ha i] at hg
    have hkey : ((expI : ℂ) ^ w₀.coord i - 1) • (a + y)
        = ((expI : ℂ) ^ w₀.coord i) • y - repGauge (gaugeTorusGen i) y := by
      rw [sub_smul, one_smul, smul_add, ← hsum]
      abel
    have hmem : (a + y) ∈ (⨆ w ∈ s', dV.piece w) ⊔ S := by
      have h1 : ((expI : ℂ) ^ w₀.coord i - 1) • (a + y) ∈ (⨆ w ∈ s', dV.piece w) ⊔ S := by
        rw [hkey]
        exact Submodule.sub_mem _ (Submodule.smul_mem _ _ hy) (hmap ⟨y, hy, rfl⟩)
      have h2 := Submodule.smul_mem _ (((expI : ℂ) ^ w₀.coord i - 1)⁻¹) h1
      rwa [smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hc1), one_smul] at h2
    exact ih (fun w hw => hs w (Finset.mem_insert_of_mem hw)) (a + y) hmem hinv

/-- A gauge-invariant element of `h.derivSubmodule n ⊔ S`, for any submodule `S` closed under
  the gauge action, already lies in `S`. The fermionic part carries no gauge singlet, since
  each of the ten species has a fixed nonzero hypercharge, so it cannot survive; what is left
  is the part in `S`. Compare `derivSubmoduleGaugeWeight_piece_zero`. -/
lemma mem_of_invariant_of_mem_derivSubmodule_sup {n : ℕ} {S : Submodule ℂ B}
    (hS : ∀ (g : GaugeGroupI) (y : B), y ∈ S → repGauge g y ∈ S)
    {x : B} (hx : x ∈ h.derivSubmodule n ⊔ S)
    (hinv : ∀ g : GaugeGroupI, repGauge g x = x) : x ∈ S := by
  refine mem_of_invariant_of_mem_biSup_piece_sup (h.derivSubmoduleGaugeWeight n) hS 3
    (h.derivSubmoduleGaugeWeight n).supp ?_ x ?_ hinv
  · have hhc : ∀ w ∈ fermionGaugeWeights, w.2.2.2 ≠ 0 := by decide
    intro w hw
    rw [GaugeWeight.coord_three]
    exact hhc w (h.derivSubmoduleGaugeWeight_supp n ▸ hw)
  · refine sup_le_sup_right
      (le_trans (le_of_eq (h.derivSubmoduleGaugeWeight n).iSup_piece.symm) ?_) S hx
    refine iSup_le fun w => ?_
    by_cases hw : w ∈ (h.derivSubmoduleGaugeWeight n).supp
    · exact le_iSup₂_of_le w hw le_rfl
    · rw [(h.derivSubmoduleGaugeWeight n).piece_eq_bot w hw]
      exact bot_le

/-- Mass weight one contributes nothing to a join: the submodule is trivial, so no invariance
  hypothesis is needed. -/
lemma mem_of_mem_massWeightSubmoduleOne_sup {S : Submodule ℂ B}
    {x : B} (hx : x ∈ h.massWeightSubmodule 1 ⊔ S) : x ∈ S := by
  rwa [h.massWeightSubmodule_one_eq, bot_sup_eq] at hx

/-- Mass weight two contributes nothing to a join: the submodule is trivial, so no invariance
  hypothesis is needed. -/
lemma mem_of_mem_massWeightSubmoduleTwo_sup {S : Submodule ℂ B}
    {x : B} (hx : x ∈ h.massWeightSubmodule 2 ⊔ S) : x ∈ S := by
  rwa [h.massWeightSubmodule_two_eq, bot_sup_eq] at hx

/-- Mass weight four contributes nothing to a join: the submodule is trivial, so no
  invariance hypothesis is needed. -/
lemma mem_of_mem_massWeightSubmoduleFour_sup {S : Submodule ℂ B}
    {x : B} (hx : x ∈ h.massWeightSubmodule 4 ⊔ S) : x ∈ S := by
  rwa [h.massWeightSubmodule_four_eq, bot_sup_eq] at hx

/-- A gauge-invariant element of `h.massWeightSubmodule 3 ⊔ S`, for `S` closed under the
  gauge action, lies in `S`: mass weight three is the underived fermion towers, which carry
  no gauge singlet. -/
lemma mem_of_invariant_of_mem_massWeightSubmoduleThree_sup {S : Submodule ℂ B}
    (hS : ∀ (g : GaugeGroupI) (y : B), y ∈ S → repGauge g y ∈ S)
    {x : B} (hx : x ∈ h.massWeightSubmodule 3 ⊔ S)
    (hinv : ∀ g : GaugeGroupI, repGauge g x = x) : x ∈ S :=
  h.mem_of_invariant_of_mem_derivSubmodule_sup hS
    (by rwa [h.massWeightSubmodule_three_eq] at hx) hinv

/-- A gauge-invariant element of `h.massWeightSubmodule 5 ⊔ S`, for `S` closed under the
  gauge action, lies in `S`: mass weight five is the once-derived fermion towers, which carry
  no gauge singlet. -/
lemma mem_of_invariant_of_mem_massWeightSubmoduleFive_sup {S : Submodule ℂ B}
    (hS : ∀ (g : GaugeGroupI) (y : B), y ∈ S → repGauge g y ∈ S)
    {x : B} (hx : x ∈ h.massWeightSubmodule 5 ⊔ S)
    (hinv : ∀ g : GaugeGroupI, repGauge g x = x) : x ∈ S :=
  h.mem_of_invariant_of_mem_derivSubmodule_sup hS
    (by rwa [h.massWeightSubmodule_five_eq] at hx) hinv

/-- A gauge-invariant element of `h.massWeightSubmodule 7 ⊔ S`, for `S` closed under the
  gauge action, lies in `S`: mass weight seven is the twice-derived fermion towers, which
  carry no gauge singlet. -/
lemma mem_of_invariant_of_mem_massWeightSubmoduleSeven_sup {S : Submodule ℂ B}
    (hS : ∀ (g : GaugeGroupI) (y : B), y ∈ S → repGauge g y ∈ S)
    {x : B} (hx : x ∈ h.massWeightSubmodule 7 ⊔ S)
    (hinv : ∀ g : GaugeGroupI, repGauge g x = x) : x ∈ S :=
  h.mem_of_invariant_of_mem_derivSubmodule_sup hS
    (by rwa [h.massWeightSubmodule_seven_eq] at hx) hinv

end IsFermionSector

end StandardModel
