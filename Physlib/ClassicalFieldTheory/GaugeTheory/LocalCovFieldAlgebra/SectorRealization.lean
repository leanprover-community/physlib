/-
Copyright (c) 2026 Nathaneal Sajan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaneal Sajan
-/
module

public import Physlib.ClassicalFieldTheory.GaugeTheory.LocalCovFieldAlgebra.Realization
public import Physlib.ClassicalFieldTheory.GaugeTheory.LocalCovFieldAlgebra.Sector
/-!
# Realizations of the covariant sector algebras

## i. Overview

A complex algebra `B` carries the covariant sector `S` of a field datum when the covariant
sector algebra `T.CovSectorAlgebra S` maps into it by a complex algebra map equivariant for
the ordinary gauge group `G₀` and for the Lorentz group, both acting on `B` by algebra
endomorphisms: `GaugeFieldData.CovSectorAlgebra.Realization`. The source gauge action is the
jet action at the constant jets; the source Lorentz action exists under
`GaugeFieldData.GaugeLorentzCompatible`, which the type carries.

A covariant sector algebra is not free on its towers, so only uniqueness from the tower
images is asserted (`Realization.ext_towers`). Realizations restrict along
`Subalgebra.inclusion` into a covariant sector from the covariant field algebra, from a larger
covariant sector, and from the local field algebra, with `G₀` acting on the target through the
constant jets; successive restrictions agree with the direct ones. An ordinary sector
realization does not restrict to the covariant sector of the same selection, which need not
lie in it.

`GaugeFieldData.PureJetsActTrivially` is used only in `Realization.map_repJet`.

## ii. Key results

- `GaugeFieldData.CovSectorAlgebra.Realization` : an algebra carrying a covariant sector.
- `GaugeFieldData.CovSectorAlgebra.Realization.restrict` : restriction to a smaller sector,
  with `restrict_restrict`.
- `GaugeFieldData.LocalCovFieldAlgebra.Realization.restrictSector` : restriction of a
  realization of the covariant field algebra to a sector, with its tower computation rules
  and `restrict_restrictSector`.
- `GaugeFieldData.Realization.restrictCovSector` : restriction of a realization of the local
  field algebra to a covariant sector, with `restrictSector_restrict` identifying it with
  the restriction through the covariant field algebra.

## iii. Table of contents

- A. Sector realizations
- B. Restriction to a smaller sector
- C. Restriction from the covariant field algebra
- D. Restriction from the local field algebra

-/

@[expose] public section

open TensorProduct Matrix MatrixGroups Lorentz

namespace GaugeFieldData

variable {G₀ : Type} [Group G₀] {𝔤 : Type} [LieRing 𝔤] [LieAlgebra ℝ 𝔤] [Module.Finite ℝ 𝔤]
  {GJ : Type} [Group GJ] {𝔤J : Type} [LieRing 𝔤J] [LieAlgebra ℝ 𝔤J]
  {jets : LocalGaugeData G₀ 𝔤 GJ 𝔤J} {T : GaugeFieldData jets}

namespace CovSectorAlgebra

/-!

## A. Sector realizations

-/

/-- A complex algebra `B` carrying the covariant sector `S` of the datum `T`: a complex
  algebra map out of the covariant sector algebra, equivariant for the ordinary gauge group
  and the Lorentz group, both acting on the whole of `B` by algebra endomorphisms. The source
  Lorentz action needs `hGL`; no other species condition is used. The lemmas `map_repValue`,
  `map_repLorentz`, `repGauge_mul` and `repLorentz_mul` name its fields. -/
abbrev Realization (T : GaugeFieldData jets) (S : Finset FieldCategory)
    (hGL : T.GaugeLorentzCompatible) (B : Type) [Semiring B] [Algebra ℂ B]
    (repGauge : Representation ℂ G₀ B) (repLorentz : Representation ℂ SL(2,ℂ) B) :=
  Representation.EquivariantAlgHom (repValue T S) repGauge (repLorentzGroup T S hGL) repLorentz

namespace Realization

variable {S : Finset FieldCategory} {B : Type} [Semiring B] [Algebra ℂ B]
  {repGauge : Representation ℂ G₀ B} {repLorentz : Representation ℂ SL(2,ℂ) B}
  {hGL : T.GaugeLorentzCompatible}

variable (T S hGL) in
/-- A covariant sector algebra realized in itself, by the identity. -/
noncomputable def id :
    Realization T S hGL (T.CovSectorAlgebra S) (repValue T S) (repLorentzGroup T S hGL) :=
  Representation.EquivariantAlgHom.id _ _ repValue_apply_mul (repLorentzGroup_apply_mul hGL)

@[simp]
lemma id_toAlgHom : (id T S hGL).toAlgHom = AlgHom.id ℂ (T.CovSectorAlgebra S) := rfl

variable (k : Realization T S hGL B repGauge repLorentz)

lemma map_repValue (g : G₀) (x : T.CovSectorAlgebra S) :
    k.toAlgHom (repValue T S g x) = repGauge g (k.toAlgHom x) :=
  k.map_fst g x

lemma map_repLorentz (Λ : SL(2,ℂ)) (x : T.CovSectorAlgebra S) :
    k.toAlgHom (repLorentzGroup T S hGL Λ x) = repLorentz Λ (k.toAlgHom x) :=
  k.map_snd Λ x

include k in
lemma repGauge_mul (g : G₀) (b₁ b₂ : B) :
    repGauge g (b₁ * b₂) = repGauge g b₁ * repGauge g b₂ :=
  k.fst_mul g b₁ b₂

include k in
lemma repLorentz_mul (Λ : SL(2,ℂ)) (b₁ b₂ : B) :
    repLorentz Λ (b₁ * b₂) = repLorentz Λ b₁ * repLorentz Λ b₂ :=
  k.snd_mul Λ b₁ b₂

/-- A sector realization is determined by its images of the selected towers; uniqueness
  only, the algebra not being free on its towers. -/
lemma ext_towers {k₁ k₂ : Realization T S hGL B repGauge repLorentz}
    (hF : ∀ (hS : FieldCategory.gauge ∈ S) (l : List (Fin 1 ⊕ Fin 3)) (μ ν : Fin 1 ⊕ Fin 3)
      (φ : Module.Dual ℝ 𝔤),
      k₁.toAlgHom ⟨T.covDerivFieldStrength l μ ν φ, covDerivFieldStrength_mem hS l μ ν φ⟩
        = k₂.toAlgHom ⟨T.covDerivFieldStrength l μ ν φ, covDerivFieldStrength_mem hS l μ ν φ⟩)
    (hψ : ∀ (hS : FieldCategory.fermion ∈ S) (i : T.FermionSpecies) {n : ℕ}
      (l : Fin n → (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (T.FermionValue i)),
      k₁.toAlgHom ⟨T.covDerivFermion i l φ, covDerivFermion_mem hS i l φ⟩
        = k₂.toAlgHom ⟨T.covDerivFermion i l φ, covDerivFermion_mem hS i l φ⟩)
    (hψc : ∀ (hS : FieldCategory.fermion ∈ S) (i : T.FermionSpecies) {n : ℕ}
      (l : Fin n → (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (ConjModule (T.FermionValue i))),
      k₁.toAlgHom ⟨T.covDerivConjFermion i l φ, covDerivConjFermion_mem hS i l φ⟩
        = k₂.toAlgHom ⟨T.covDerivConjFermion i l φ, covDerivConjFermion_mem hS i l φ⟩)
    (hφ : ∀ (hS : FieldCategory.scalar ∈ S) (j : T.BosonSpecies) {n : ℕ}
      (l : Fin n → (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (T.BosonValue j)),
      k₁.toAlgHom ⟨T.covDerivBoson j l φ, covDerivBoson_mem hS j l φ⟩
        = k₂.toAlgHom ⟨T.covDerivBoson j l φ, covDerivBoson_mem hS j l φ⟩)
    (hφc : ∀ (hS : FieldCategory.scalar ∈ S) (j : T.BosonSpecies) {n : ℕ}
      (l : Fin n → (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (ConjModule (T.BosonValue j))),
      k₁.toAlgHom ⟨T.covDerivConjBoson j l φ, covDerivConjBoson_mem hS j l φ⟩
        = k₂.toAlgHom ⟨T.covDerivConjBoson j l φ, covDerivConjBoson_mem hS j l φ⟩) :
    k₁ = k₂ :=
  Representation.EquivariantAlgHom.ext (algHom_ext hF hψ hψc hφ hφc)

/-- Under `GaugeFieldData.PureJetsActTrivially` the jet action factors through evaluation:
  a jet acts on the realized image as its value. -/
lemma map_repJet (hP : T.PureJetsActTrivially) (U : GJ) (x : T.CovSectorAlgebra S) :
    k.toAlgHom (repJet T S U x) = repGauge (jets.eval U) (k.toAlgHom x) := by
  rw [repJet_eq_repValue_eval hP, k.map_repValue]

/-!

## B. Restriction to a smaller sector

-/

variable {S' : Finset FieldCategory}

/-- The restriction of a covariant sector realization to a smaller sector. -/
noncomputable def restrict (k : Realization T S' hGL B repGauge repLorentz) (hS : S ⊆ S') :
    Realization T S hGL B repGauge repLorentz :=
  k.comp (Subalgebra.inclusion (mono T hS)) (inclusion_repValue hS)
    (inclusion_repLorentzGroup hS hGL)

lemma restrict_toAlgHom (k : Realization T S' hGL B repGauge repLorentz) (hS : S ⊆ S') :
    (k.restrict hS).toAlgHom = k.toAlgHom.comp (Subalgebra.inclusion (mono T hS)) := rfl

@[simp]
lemma restrict_toAlgHom_apply (k : Realization T S' hGL B repGauge repLorentz) (hS : S ⊆ S')
    (x : T.CovSectorAlgebra S) :
    (k.restrict hS).toAlgHom x = k.toAlgHom (Subalgebra.inclusion (mono T hS) x) := rfl

lemma restrict_toAlgHom_mk (k : Realization T S' hGL B repGauge repLorentz) (hS : S ⊆ S')
    (x : T.LocalFieldAlgebra) (hx : x ∈ T.CovSectorAlgebra S) :
    (k.restrict hS).toAlgHom ⟨x, hx⟩ = k.toAlgHom ⟨x, mono T hS hx⟩ := rfl

lemma restrict_id_toAlgHom (hS : S ⊆ S') :
    ((id T S' hGL).restrict hS).toAlgHom = Subalgebra.inclusion (mono T hS) :=
  AlgHom.ext fun _ => rfl

lemma restrict_restrict {S'' : Finset FieldCategory}
    (k : Realization T S'' hGL B repGauge repLorentz) (hS' : S' ⊆ S'') (hS : S ⊆ S') :
    (k.restrict hS').restrict hS = k.restrict (hS.trans hS') :=
  -- Stated through the computation rules: a bare `rfl` sends the kernel into a timeout.
  Representation.EquivariantAlgHom.ext (AlgHom.ext fun x => by
    simp only [restrict_toAlgHom_apply, Subalgebra.inclusion_inclusion])

end Realization

end CovSectorAlgebra

/-!

## C. Restriction from the covariant field algebra

-/

namespace LocalCovFieldAlgebra.Realization

variable {B : Type} [Semiring B] [Algebra ℂ B] {repGauge : Representation ℂ G₀ B}
  {repLorentz : Representation ℂ SL(2,ℂ) B} {hGL : T.GaugeLorentzCompatible}
  (k : Realization T hGL B repGauge repLorentz) (S : Finset FieldCategory)

/-- The restriction of a realization of the covariant field algebra to a covariant sector. -/
noncomputable def restrictSector : CovSectorAlgebra.Realization T S hGL B repGauge repLorentz :=
  k.comp (Subalgebra.inclusion (CovSectorAlgebra.le_localCovFieldAlgebra T S))
    CovSectorAlgebra.inclusion_localCovFieldAlgebra_repValue
    (CovSectorAlgebra.inclusion_localCovFieldAlgebra_repLorentzGroup hGL)

lemma restrictSector_toAlgHom :
    (k.restrictSector S).toAlgHom
      = k.toAlgHom.comp (Subalgebra.inclusion (CovSectorAlgebra.le_localCovFieldAlgebra T S)) :=
  rfl

@[simp]
lemma restrictSector_toAlgHom_apply (x : T.CovSectorAlgebra S) :
    (k.restrictSector S).toAlgHom x
      = k.toAlgHom (Subalgebra.inclusion (CovSectorAlgebra.le_localCovFieldAlgebra T S) x) :=
  rfl

lemma restrictSector_id_toAlgHom :
    ((id T hGL).restrictSector S).toAlgHom
      = Subalgebra.inclusion (CovSectorAlgebra.le_localCovFieldAlgebra T S) :=
  AlgHom.ext fun _ => rfl

lemma restrictSector_fieldStrength (hS : FieldCategory.gauge ∈ S) (l : List (Fin 1 ⊕ Fin 3))
    (μ ν : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ 𝔤) :
    (k.restrictSector S).toAlgHom
      ⟨T.covDerivFieldStrength l μ ν φ, CovSectorAlgebra.covDerivFieldStrength_mem hS l μ ν φ⟩
      = k.fieldStrength l μ ν φ := rfl

lemma restrictSector_fermion (hS : FieldCategory.fermion ∈ S) (i : T.FermionSpecies) {n : ℕ}
    (l : Fin n → (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (T.FermionValue i)) :
    (k.restrictSector S).toAlgHom
      ⟨T.covDerivFermion i l φ, CovSectorAlgebra.covDerivFermion_mem hS i l φ⟩
      = k.fermion i l φ := rfl

lemma restrictSector_conjFermion (hS : FieldCategory.fermion ∈ S) (i : T.FermionSpecies)
    {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (ConjModule (T.FermionValue i))) :
    (k.restrictSector S).toAlgHom
      ⟨T.covDerivConjFermion i l φ, CovSectorAlgebra.covDerivConjFermion_mem hS i l φ⟩
      = k.conjFermion i l φ := rfl

lemma restrictSector_boson (hS : FieldCategory.scalar ∈ S) (j : T.BosonSpecies) {n : ℕ}
    (l : Fin n → (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (T.BosonValue j)) :
    (k.restrictSector S).toAlgHom
      ⟨T.covDerivBoson j l φ, CovSectorAlgebra.covDerivBoson_mem hS j l φ⟩
      = k.boson j l φ := rfl

lemma restrictSector_conjBoson (hS : FieldCategory.scalar ∈ S) (j : T.BosonSpecies) {n : ℕ}
    (l : Fin n → (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (ConjModule (T.BosonValue j))) :
    (k.restrictSector S).toAlgHom
      ⟨T.covDerivConjBoson j l φ, CovSectorAlgebra.covDerivConjBoson_mem hS j l φ⟩
      = k.conjBoson j l φ := rfl

lemma restrict_restrictSector {S' : Finset FieldCategory} (hS : S ⊆ S') :
    (k.restrictSector S').restrict hS = k.restrictSector S :=
  Representation.EquivariantAlgHom.ext (AlgHom.ext fun x => by
    simp only [CovSectorAlgebra.Realization.restrict_toAlgHom_apply,
      restrictSector_toAlgHom_apply, Subalgebra.inclusion_inclusion])

end LocalCovFieldAlgebra.Realization

/-!

## D. Restriction from the local field algebra

-/

namespace Realization

variable {B : Type} [Ring B] [Algebra ℂ B] {repJet : Representation ℂ GJ B}
  {repLorentz : Representation ℂ SL(2,ℂ) B} (h : Realization T B repJet repLorentz)
  (hGL : T.GaugeLorentzCompatible) (S : Finset FieldCategory)

/-- The restriction of a realization of the local field algebra to a covariant sector; the
  ordinary gauge group acts on the target through the constant jets. -/
noncomputable def restrictCovSector :
    CovSectorAlgebra.Realization T S hGL B (repJet.comp jets.ofConstant) repLorentz :=
  (h.restrictSubalgebra (T.CovSectorAlgebra S)
    (fun U _ hx => CovSectorAlgebra.repJet_mem U hx)
    (fun Λ _ hx => CovSectorAlgebra.repLorentzGroup_mem hGL Λ hx)).compFst jets.ofConstant

lemma restrictCovSector_toAlgHom :
    (h.restrictCovSector hGL S).toAlgHom = h.toAlgHom.comp (T.CovSectorAlgebra S).val := rfl

@[simp]
lemma restrictCovSector_toAlgHom_apply (x : T.CovSectorAlgebra S) :
    (h.restrictCovSector hGL S).toAlgHom x = h.toAlgHom x := rfl

/-- Jet equivariance survives restriction without `PureJetsActTrivially`. -/
lemma restrictCovSector_map_repJet (U : GJ) (x : T.CovSectorAlgebra S) :
    (h.restrictCovSector hGL S).toAlgHom (CovSectorAlgebra.repJet T S U x)
      = repJet U ((h.restrictCovSector hGL S).toAlgHom x) :=
  h.map_repJet U x

/-- Restriction through the covariant field algebra is the direct restriction. -/
lemma restrictSector_restrict :
    (h.restrict hGL).restrictSector S = h.restrictCovSector hGL S :=
  Representation.EquivariantAlgHom.ext (by
    rw [LocalCovFieldAlgebra.Realization.restrictSector_toAlgHom, restrict_toAlgHom,
      restrictCovSector_toAlgHom, AlgHom.comp_assoc, Subalgebra.val_comp_inclusion])

lemma restrict_restrictCovSector {S' : Finset FieldCategory} (hS : S ⊆ S') :
    (h.restrictCovSector hGL S').restrict hS = h.restrictCovSector hGL S := by
  rw [← restrictSector_restrict, ← restrictSector_restrict,
    LocalCovFieldAlgebra.Realization.restrict_restrictSector]

end Realization

end GaugeFieldData
