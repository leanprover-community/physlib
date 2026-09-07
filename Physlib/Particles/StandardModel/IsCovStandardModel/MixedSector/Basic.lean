/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.IsCovStandardModel.Sectors
/-!
# The mixed sector

The `{gauge, higgs, fermion}` three-class sector of `Sectors.lean` is the home of any
term that mixes all three kinds of covariant field at once. Its words are the least
weighty of any two- or three-class sector: a field-strength tower carries weight at
least `4`, a Higgs (or conjugate Higgs) tower weight at least `2`, and a fermion tower
weight at least `3`, so a word realising all three classes has total weight at least
`4 + 2 + 3 = 9`.

Consequently the mixed sector vanishes identically below weight nine
(`sectorMassWeight_mixed_eq_bot_of_lt_nine`) — in particular at every weight up to
eight, i.e. there is no Standard-Model term of mass dimension at most four (mass
weight, twice the mass dimension, at most eight) that mixes gauge, Higgs and fermion
fields together.

Below weight nine, then, there is nothing left to classify. The sector is `⊥`, so an
element of `⊥ ⊔ S` is an element of `S` outright, whatever `S` may be. Section B records
that in the shape the other sectors carry, so that the four can later be combined; unlike
them it asks no stability of `S` and no invariance of the element, there being nothing to
peel away and no parity or index count to run.

- A. The mixed sector vanishes below weight nine
- B. The classification below weight nine

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
  {bard : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) →
    Module.Dual ℂ (ConjModule DownSinglet) →ₗ[ℂ] B}
  {u : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ UpSinglet →ₗ[ℂ] B}
  {baru : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ (ConjModule UpSinglet) →ₗ[ℂ] B}
  {Q : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ QuarkDoublet →ₗ[ℂ] B}
  {barQ : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) →
    Module.Dual ℂ (ConjModule QuarkDoublet) →ₗ[ℂ] B}
  {L : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ LeptonDoublet →ₗ[ℂ] B}
  {barL : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) →
    Module.Dual ℂ (ConjModule LeptonDoublet) →ₗ[ℂ] B}
  {e : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ LeptonSinglet →ₗ[ℂ] B}
  {bare : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) →
    Module.Dual ℂ (ConjModule LeptonSinglet) →ₗ[ℂ] B}
  (h : IsCovStandardModel B repGauge hrepGauge_mul repLorentz hrepLorentz_mul
    massWeightPoly H barH F d bard u baru Q barQ L barL e bare)

/-!

## A. The mixed sector vanishes below weight nine

-/

/-- The mixed sector vanishes below weight nine: a word realising all three
  classes carries gauge weight at least four, Higgs weight at least two and fermion
  weight at least three, for a total of at least nine — so no such word exists at a
  lower weight, and the sector's span there is trivial. -/
lemma sectorMassWeight_mixed_eq_bot_of_lt_nine {w : ℕ} (hw : w < 9) :
    h.sectorMassWeight
      {GeneratorClass.gauge, GeneratorClass.higgs, GeneratorClass.fermion} w = ⊥ := by
  rw [sectorMassWeight, Submodule.span_eq_bot]
  rintro x ⟨gl, hS, hsum, rfl⟩
  exfalso
  have hgauge : GeneratorClass.gauge ∈ wordClasses gl := by rw [hS]; simp
  have hhiggs : GeneratorClass.higgs ∈ wordClasses gl := by rw [hS]; simp
  have hfermion : GeneratorClass.fermion ∈ wordClasses gl := by rw [hS]; simp
  have h1 := le_classWeight_of_mem hgauge (fun g hg => Generators.four_le_weight_of_gauge hg)
  have h2 := le_classWeight_of_mem hhiggs (fun g hg => Generators.two_le_weight_of_higgs hg)
  have h3 := le_classWeight_of_mem hfermion (fun g hg => Generators.three_le_weight_of_fermion hg)
  have h4 := classWeight_add_three gl
  omega

/-- The weight-eight mixed sector vanishes: the mass weight of a dimension-four
  Standard-Model term is at most eight, and the mixed sector is trivial there — no
  dimension-four term mixes gauge, Higgs and fermion fields together. -/
lemma sectorMassWeight_mixed_eight :
    h.sectorMassWeight {GeneratorClass.gauge, GeneratorClass.higgs, GeneratorClass.fermion} 8
      = ⊥ :=
  h.sectorMassWeight_mixed_eq_bot_of_lt_nine (by omega)

/-!

## B. The classification below weight nine

Nine is beyond every weight a dimension-four term can reach, so the vanishing of section A
settles the whole of the mixed sector at a stroke: an element of `⊥ ⊔ S` is an element of
`S`. The three statements below are those of the gauge and Yukawa sectors, name for name,
so that the four sectors can be combined uniformly. There the forward direction is an
argument — a metric trace, an index count, a boost-weight parity — and needs `S` stable
and the element invariant; here it is the emptiness of the sector, and the invariance
conjuncts ride along in the equivalences only to keep the shapes matched.

-/

/-- Below mass weight nine the mixed sector adds nothing to a submodule `S`: an element of
  `sectorMassWeight {gauge, higgs, fermion} w ⊔ S` for `w < 9` already lies in `S`. The
  sector is trivial there, so no invariance is asked of `x` and no stability of `S`. -/
theorem mem_of_invariant_sectorMassWeight_mixed_lt_nine_sup (w : ℕ) (hw : w < 9)
    (S : Submodule ℂ B) {x : B}
    (hx : x ∈ h.sectorMassWeight {GeneratorClass.gauge, GeneratorClass.higgs,
      GeneratorClass.fermion} w ⊔ S) : x ∈ S := by
  rwa [h.sectorMassWeight_mixed_eq_bot_of_lt_nine hw, bot_sup_eq] at hx

/-- The classification below mass weight nine as an equivalence, in the shape of the
  gauge- and Yukawa-sector statements: an element of
  `sectorMassWeight {gauge, higgs, fermion} w ⊔ S` for `w < 9` is fixed by both groups
  exactly when it is itself an element of `S` fixed by both groups. Neither stability
  hypothesis on `S` is needed, the forward direction being the vanishing of the sector. -/
theorem mem_sectorMassWeight_mixed_lt_nine_sup_and_gauge_lorentz_invariant_iff (w : ℕ)
    (hw : w < 9) (S : Submodule ℂ B) (x : B) :
    (x ∈ h.sectorMassWeight {GeneratorClass.gauge, GeneratorClass.higgs,
          GeneratorClass.fermion} w ⊔ S
        ∧ (∀ g : GaugeGroupI, repGauge g x = x) ∧ ∀ g : SL(2,ℂ), repLorentz g x = x)
      ↔ ∃ y ∈ S, (∀ g : GaugeGroupI, repGauge g y = y)
          ∧ (∀ g : SL(2,ℂ), repLorentz g y = y)
          ∧ x = y := by
  constructor
  · rintro ⟨hx, hG, hL⟩
    exact ⟨x, h.mem_of_invariant_sectorMassWeight_mixed_lt_nine_sup w hw S hx, hG, hL, rfl⟩
  · rintro ⟨y, hyS, hyG, hyL, rfl⟩
    exact ⟨Submodule.mem_sup_right hyS, hyG, hyL⟩

/-- The same classification without the existential: below mass weight nine an element of
  `sectorMassWeight {gauge, higgs, fermion} w ⊔ S` fixed by both groups is an element of
  `S` fixed by both groups, and conversely. -/
theorem mem_sectorMassWeight_mixed_lt_nine_sup_and_gauge_lorentz_invariant_iff_mem (w : ℕ)
    (hw : w < 9) (S : Submodule ℂ B) (x : B) :
    (x ∈ h.sectorMassWeight {GeneratorClass.gauge, GeneratorClass.higgs,
          GeneratorClass.fermion} w ⊔ S
        ∧ (∀ g : GaugeGroupI, repGauge g x = x) ∧ ∀ g : SL(2,ℂ), repLorentz g x = x)
      ↔ (x ∈ S ∧ (∀ g : GaugeGroupI, repGauge g x = x)
          ∧ ∀ g : SL(2,ℂ), repLorentz g x = x) :=
  ⟨fun hx => ⟨h.mem_of_invariant_sectorMassWeight_mixed_lt_nine_sup w hw S hx.1, hx.2⟩,
    fun hx => ⟨Submodule.mem_sup_right hx.1, hx.2⟩⟩

end IsCovStandardModel

end StandardModel
