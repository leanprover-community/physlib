/-
Copyright (c) 2026 Nathaneal Sajan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaneal Sajan
-/
module

public import Physlib.ClassicalFieldTheory.GaugeTheory.LocalFieldAlgebra.Realization
public import Physlib.ClassicalFieldTheory.GaugeTheory.LocalFieldAlgebra.Sector
/-!
# Realizations of the ordinary sector algebras

## i. Overview

A complex algebra `B` carries the ordinary sector `S` of a field datum when the sector
algebra `T.SectorAlgebra S` maps into it by a complex algebra map equivariant for the jet
gauge group and the Lorentz group, both acting on `B` by algebra endomorphisms:
`GaugeFieldData.SectorAlgebra.Realization`. No species condition is involved.

A sector realization is determined by its images of the selected generators
(`Realization.ext_generators`); nothing asserts that an arbitrary assignment of those images
extends to a realization. Realizations restrict along `Subalgebra.inclusion` from the local
field algebra to every sector and from a sector to every smaller one, and successive
restrictions agree with the direct one.

## ii. Key results

- `GaugeFieldData.SectorAlgebra.Realization` : an algebra carrying an ordinary sector.
- `GaugeFieldData.SectorAlgebra.Realization.restrict` : restriction to a smaller sector,
  with `restrict_restrict`.
- `GaugeFieldData.Realization.restrictSector` : restriction of a realization of the local
  field algebra to a sector, with `restrict_restrictSector`.

## iii. Table of contents

- A. Sector realizations
- B. Restriction to a smaller sector
- C. Restriction from the local field algebra

-/

@[expose] public section

open TensorProduct Matrix MatrixGroups

namespace GaugeFieldData

variable {G₀ : Type} [Group G₀] {𝔤 : Type} [LieRing 𝔤] [LieAlgebra ℝ 𝔤] [Module.Finite ℝ 𝔤]
  {GJ : Type} [Group GJ] {𝔤J : Type} [LieRing 𝔤J] [LieAlgebra ℝ 𝔤J]
  {jets : LocalGaugeData G₀ 𝔤 GJ 𝔤J} {T : GaugeFieldData jets}

namespace SectorAlgebra

/-!

## A. Sector realizations

-/

/-- A complex algebra `B` carrying the ordinary sector `S` of the datum `T`: a complex
  algebra map out of the sector algebra, equivariant for the jet gauge group and the Lorentz
  group, both acting on the whole of `B` by algebra endomorphisms. The lemmas `map_repJet`,
  `map_repLorentz`, `repJet_mul` and `repLorentz_mul` name its fields. -/
abbrev Realization (T : GaugeFieldData jets) (S : Finset FieldCategory) (B : Type)
    [Semiring B] [Algebra ℂ B] (repJet : Representation ℂ GJ B)
    (repLorentz : Representation ℂ SL(2,ℂ) B) :=
  Representation.EquivariantAlgHom (SectorAlgebra.repJet T S) repJet
    (SectorAlgebra.repLorentzGroup T S) repLorentz

namespace Realization

variable {S : Finset FieldCategory} {B : Type} [Semiring B] [Algebra ℂ B]
  {repJet : Representation ℂ GJ B} {repLorentz : Representation ℂ SL(2,ℂ) B}

variable (T S) in
/-- A sector algebra realized in itself, by the identity. -/
noncomputable def id :
    Realization T S (T.SectorAlgebra S) (SectorAlgebra.repJet T S)
      (SectorAlgebra.repLorentzGroup T S) :=
  Representation.EquivariantAlgHom.id _ _ repJet_apply_mul repLorentzGroup_apply_mul

@[simp]
lemma id_toAlgHom : (id T S).toAlgHom = AlgHom.id ℂ (T.SectorAlgebra S) := rfl

variable (h : Realization T S B repJet repLorentz)

lemma map_repJet (U : GJ) (x : T.SectorAlgebra S) :
    h.toAlgHom (SectorAlgebra.repJet T S U x) = repJet U (h.toAlgHom x) :=
  h.map_fst U x

lemma map_repLorentz (Λ : SL(2,ℂ)) (x : T.SectorAlgebra S) :
    h.toAlgHom (SectorAlgebra.repLorentzGroup T S Λ x) = repLorentz Λ (h.toAlgHom x) :=
  h.map_snd Λ x

include h in
lemma repJet_mul (U : GJ) (b₁ b₂ : B) : repJet U (b₁ * b₂) = repJet U b₁ * repJet U b₂ :=
  h.fst_mul U b₁ b₂

include h in
lemma repLorentz_mul (Λ : SL(2,ℂ)) (b₁ b₂ : B) :
    repLorentz Λ (b₁ * b₂) = repLorentz Λ b₁ * repLorentz Λ b₂ :=
  h.snd_mul Λ b₁ b₂

/-- A sector realization is determined by its images of the selected generators. Only
  uniqueness is asserted, not the extension of an arbitrary assignment. -/
lemma ext_generators {h₁ h₂ : Realization T S B repJet repLorentz}
    (hf : ∀ (hS : FieldCategory.fermion ∈ S) (v : T.FermionGenerators),
      h₁.toAlgHom ⟨T.ιFermionTotal v, ιFermionTotal_mem hS v⟩
        = h₂.toAlgHom ⟨T.ιFermionTotal v, ιFermionTotal_mem hS v⟩)
    (hs : ∀ (hS : FieldCategory.scalar ∈ S) (v : T.BosonGenerators),
      h₁.toAlgHom ⟨T.ιBosonTotal v, ιBosonTotal_mem hS v⟩
        = h₂.toAlgHom ⟨T.ιBosonTotal v, ιBosonTotal_mem hS v⟩)
    (hg : ∀ (hS : FieldCategory.gauge ∈ S) (v : GaugeBoson.JetComponentSpace 𝔤),
      h₁.toAlgHom ⟨T.ιConnection v, ιConnection_mem hS v⟩
        = h₂.toAlgHom ⟨T.ιConnection v, ιConnection_mem hS v⟩) : h₁ = h₂ :=
  Representation.EquivariantAlgHom.ext (algHom_ext hf hs hg)

/-!

## B. Restriction to a smaller sector

-/

variable {S' : Finset FieldCategory}

/-- The restriction of a sector realization to a smaller sector. -/
noncomputable def restrict (h : Realization T S' B repJet repLorentz) (hS : S ⊆ S') :
    Realization T S B repJet repLorentz :=
  h.comp (Subalgebra.inclusion (mono T hS)) (inclusion_repJet hS) (inclusion_repLorentzGroup hS)

lemma restrict_toAlgHom (h : Realization T S' B repJet repLorentz) (hS : S ⊆ S') :
    (h.restrict hS).toAlgHom = h.toAlgHom.comp (Subalgebra.inclusion (mono T hS)) := rfl

@[simp]
lemma restrict_toAlgHom_apply (h : Realization T S' B repJet repLorentz) (hS : S ⊆ S')
    (x : T.SectorAlgebra S) :
    (h.restrict hS).toAlgHom x = h.toAlgHom (Subalgebra.inclusion (mono T hS) x) := rfl

lemma restrict_toAlgHom_mk (h : Realization T S' B repJet repLorentz) (hS : S ⊆ S')
    (x : T.LocalFieldAlgebra) (hx : x ∈ T.SectorAlgebra S) :
    (h.restrict hS).toAlgHom ⟨x, hx⟩ = h.toAlgHom ⟨x, mono T hS hx⟩ := rfl

lemma restrict_id_toAlgHom (hS : S ⊆ S') :
    ((id T S').restrict hS).toAlgHom = Subalgebra.inclusion (mono T hS) :=
  AlgHom.ext fun _ => rfl

lemma restrict_restrict {S'' : Finset FieldCategory} (h : Realization T S'' B repJet repLorentz)
    (hS' : S' ⊆ S'') (hS : S ⊆ S') :
    (h.restrict hS').restrict hS = h.restrict (hS.trans hS') :=
  -- Stated through the computation rules: a bare `rfl` sends the kernel into a timeout.
  Representation.EquivariantAlgHom.ext (AlgHom.ext fun x => by
    simp only [restrict_toAlgHom_apply, Subalgebra.inclusion_inclusion])

end Realization

end SectorAlgebra

/-!

## C. Restriction from the local field algebra

-/

namespace Realization

variable {B : Type} [Ring B] [Algebra ℂ B] {repJet : Representation ℂ GJ B}
  {repLorentz : Representation ℂ SL(2,ℂ) B} (h : Realization T B repJet repLorentz)
  (S : Finset FieldCategory)

/-- The restriction of a realization of the local field algebra to a sector. -/
noncomputable def restrictSector : SectorAlgebra.Realization T S B repJet repLorentz :=
  h.restrictSubalgebra (T.SectorAlgebra S) (fun U _ hx => SectorAlgebra.repJet_mem U hx)
    (fun Λ _ hx => SectorAlgebra.repLorentzGroup_mem Λ hx)

lemma restrictSector_toAlgHom :
    (h.restrictSector S).toAlgHom = h.toAlgHom.comp (T.SectorAlgebra S).val := rfl

@[simp]
lemma restrictSector_toAlgHom_apply (x : T.SectorAlgebra S) :
    (h.restrictSector S).toAlgHom x = h.toAlgHom x := rfl

lemma restrictSector_id_toAlgHom :
    ((id T).restrictSector S).toAlgHom = (T.SectorAlgebra S).val :=
  AlgHom.ext fun _ => rfl

lemma restrictSector_fermionSymbol (hS : FieldCategory.fermion ∈ S) (i : T.FermionSpecies)
    (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (T.FermionValue i)) :
    (h.restrictSector S).toAlgHom ⟨T.fermionSymbol i s φ, SectorAlgebra.fermionSymbol_mem hS i s φ⟩
      = h.fermionSymbol i s φ := rfl

lemma restrictSector_conjFermionSymbol (hS : FieldCategory.fermion ∈ S)
    (i : T.FermionSpecies) (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (ConjModule (T.FermionValue i))) :
    (h.restrictSector S).toAlgHom
      ⟨T.conjFermionSymbol i s φ, SectorAlgebra.conjFermionSymbol_mem hS i s φ⟩
      = h.conjFermionSymbol i s φ := rfl

lemma restrictSector_bosonSymbol (hS : FieldCategory.scalar ∈ S) (j : T.BosonSpecies)
    (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (T.BosonValue j)) :
    (h.restrictSector S).toAlgHom ⟨T.bosonSymbol j s φ, SectorAlgebra.bosonSymbol_mem hS j s φ⟩
      = h.bosonSymbol j s φ := rfl

lemma restrictSector_conjBosonSymbol (hS : FieldCategory.scalar ∈ S) (j : T.BosonSpecies)
    (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (ConjModule (T.BosonValue j))) :
    (h.restrictSector S).toAlgHom
      ⟨T.conjBosonSymbol j s φ, SectorAlgebra.conjBosonSymbol_mem hS j s φ⟩
      = h.conjBosonSymbol j s φ := rfl

lemma restrict_restrictSector {S' : Finset FieldCategory} (hS : S ⊆ S') :
    (h.restrictSector S').restrict hS = h.restrictSector S :=
  Representation.EquivariantAlgHom.ext (by
    rw [SectorAlgebra.Realization.restrict_toAlgHom, restrictSector_toAlgHom,
      restrictSector_toAlgHom, AlgHom.comp_assoc, Subalgebra.val_comp_inclusion])

end Realization

end GaugeFieldData
