/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.CondensedMatter.Crystal.Brillouin
public import PhyslibAlpha.ProbabilisticTheory.Representation.SectorReduction
public import PhyslibAlpha.ProbabilisticTheory.Representation.Koopman

/-!

# The translations and symmetries of a crystal on `ℓ²` of its sites

The space of square-summable functions on the sites of a crystal carries the translations and the
bond-preserving symmetries as a covariant unitary representation.

## i. Overview

The Hilbert space `ℓ²(C.Site)` of a crystal is `L²` of the counting measure on its sites. The
translations act on the sites by permutations, and so do the bond-preserving symmetries. Every
permutation preserves the counting measure, so each group acts unitarily by composition: the
Koopman representation. The two actions are compatible: a symmetry with linear part `A` carries
the translation by `a` to the translation by `A a`. This is exactly the covariance of
`PointCovariance`. The Hilbert space needs no choice of orbitals, and covers any number of sites
per cell.

Consequently the sector reduction of `SectorReduction` applies to every bounded operator on
`ℓ²(C.Site)` that commutes with the translations and the symmetries: the adjacency operator of the
bond graph, any hopping Hamiltonian with symmetric amplitudes, or the unitary group of a
Schrödinger evolution.

## ii. Key results

- `siteTranslation`, `siteSymmetry` : the actions on `ℓ²(C.Site)`.
- `siteTranslation_covariant` : the covariance of the two representations.
- `spectrum_sectorOp_eq_site` : the symmetry reduction of the spectrum of an invariant operator
  to the sectors of momentum.

## iii. Table of contents

- A. Counting measure on the sites
- B. The representations
- C. Symmetry reduction

## iv. References

* None.

-/

@[expose] public section

noncomputable section

namespace CondensedMatter

open ProbabilisticTheory ProbabilisticTheory.QuantumMechanics MeasureTheory
open CondensedMatter.Crystal

variable {G F : Type*} [AddCommGroup G]

/-! ## A. Counting measure on the sites -/

/-- Every set of sites is measurable. -/
instance : MeasurableSpace (CellSite G F) := ⊤

instance : MeasurableSingletonClass (CellSite G F) := ⟨fun _ => trivial⟩

instance [Countable G] [Countable F] : Countable (CellSite G F) :=
  Function.Injective.countable (f := fun x => (x.cell, x.label)) fun x y h => by
    exact CellSite.ext (congrArg Prod.fst h) (congrArg Prod.snd h)

/-- A permutation of a countable set preserves the counting measure. -/
lemma measurePreserving_count {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    [Countable X] (e : Equiv.Perm X) :
    MeasurePreserving e (Measure.count : Measure X) Measure.count := by
  refine ⟨measurable_of_countable _, ?_⟩
  have h1 : (Measure.count : Measure X).map e ≤ Measure.count :=
    e.injective.map_count_le (measurable_of_countable _)
  have h2 : (Measure.count : Measure X).map e.symm ≤ Measure.count :=
    e.symm.injective.map_count_le (measurable_of_countable _)
  refine le_antisymm h1 ?_
  calc (Measure.count : Measure X)
      = ((Measure.count : Measure X).map e.symm).map e := by
        rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
        have : (e : X → X) ∘ (e.symm : X → X) = id := by funext x; simp
        rw [this, Measure.map_id]
    _ ≤ (Measure.count : Measure X).map e := Measure.map_mono h2 (measurable_of_countable _)

/-! ## B. The representations -/

variable [TopologicalSpace G] [DiscreteTopology G] [Countable G] [Finite F]

/-- The square-summable functions on the sites of a crystal built from a unit cell. -/
abbrev SiteSpace (G F : Type*) :=
  Lp ℂ 2 (Measure.count : Measure (CellSite G F))

/-- The translations act on the sites by permutations. -/
def siteTranslationPerm (G F : Type*) [AddCommGroup G] :
    Multiplicative G →* Equiv.Perm (CellSite G F) :=
  MulAction.toPermHom (Multiplicative G) (CellSite G F)

/-- **The translation representation** on `ℓ²` of the sites: `(U_a ψ)(x) = ψ(-a + x)`. -/
def siteTranslation (G F : Type*) [AddCommGroup G] [Countable G] [Countable F] :
    Multiplicative G →* unitary (SiteSpace G F →L[ℂ] SiteSpace G F) :=
  UnitaryRep.koopman (E := ℂ) Measure.count (siteTranslationPerm G F)
    (fun _a => measurePreserving_count _)

variable (g : PeriodicGraph (Crystal.ofUnitCell G F))

/-- The bond-preserving symmetries act on the sites by permutations. -/
def siteSymmetryPerm : g.symmetries →* Equiv.Perm (CellSite G F) :=
  MulAction.toPermHom g.symmetries (CellSite G F)

/-- **The symmetry representation** on `ℓ²` of the sites: `(U_s ψ)(x) = ψ(s⁻¹ • x)`. -/
def siteSymmetry : g.symmetries →* unitary (SiteSpace G F →L[ℂ] SiteSpace G F) :=
  UnitaryRep.koopman (E := ℂ) Measure.count (siteSymmetryPerm g)
    (fun _s => measurePreserving_count _)

/-- The action of a symmetry on the lattice of translations, through its linear part. -/
def latticeAut : g.symmetries →* MulAut (Multiplicative G) where
  toFun s := AddEquiv.toMultiplicative (s : CellSymmetry G F).linear
  map_one' := rfl
  map_mul' _s _t := rfl

omit [DiscreteTopology G] in
omit [Countable G] in
omit [TopologicalSpace G] in
/-- A symmetry moves a translated site to the correspondingly translated image: the permutations
of the sites satisfy `s ∘ τ_a = τ_{A a} ∘ s`. -/
lemma siteSymmetryPerm_translation (s : g.symmetries) (a : Multiplicative G) :
    siteSymmetryPerm g s * siteTranslationPerm G F a =
      siteTranslationPerm G F (latticeAut g s a) * siteSymmetryPerm g s := by
  refine Equiv.ext fun x => ?_
  rcases x with ⟨n, i⟩
  refine CellSite.ext ?_ rfl
  change (s : CellSymmetry G F).linear (Multiplicative.toAdd a + n) +
    (s : CellSymmetry G F).shift i =
    (s : CellSymmetry G F).linear (Multiplicative.toAdd a) +
      ((s : CellSymmetry G F).linear n + (s : CellSymmetry G F).shift i)
  rw [map_add, add_assoc]

omit [DiscreteTopology G] in
omit [TopologicalSpace G] in
/-- **The translations and the bond-preserving symmetries form a covariant representation on
`ℓ²` of the sites.** -/
lemma siteTranslation_covariant :
    UnitaryRep.IsCovariantRep (latticeAut g) (siteTranslation G F) (siteSymmetry g) := by
  intro s a
  refine Subtype.ext (ContinuousLinearMap.ext fun f => ?_)
  have hperm := siteSymmetryPerm_translation g s a
  have hinv : siteTranslationPerm G F a⁻¹ * siteSymmetryPerm g s⁻¹ =
      siteSymmetryPerm g s⁻¹ * siteTranslationPerm G F (latticeAut g s a)⁻¹ := by
    simp only [map_inv]
    rw [← mul_inv_rev, ← mul_inv_rev, hperm]
  have hfun : ⇑(siteTranslationPerm G F a⁻¹) ∘ ⇑(siteSymmetryPerm g s⁻¹) =
      ⇑(siteSymmetryPerm g s⁻¹) ∘ ⇑(siteTranslationPerm G F (latticeAut g s a)⁻¹) := by
    funext x
    exact congrArg (fun e : Equiv.Perm (CellSite G F) => e x) hinv
  have h1 := Lp.compMeasurePreserving_comp_apply (E := ℂ) (p := 2) f
    (measurePreserving_count (siteTranslationPerm G F a⁻¹))
    (measurePreserving_count (siteSymmetryPerm g s⁻¹))
  have h2 := Lp.compMeasurePreserving_comp_apply (E := ℂ) (p := 2) f
    (measurePreserving_count (siteSymmetryPerm g s⁻¹))
    (measurePreserving_count (siteTranslationPerm G F (latticeAut g s a)⁻¹))
  simp only [siteTranslation, siteSymmetry, Submonoid.coe_mul, mul_apply_eq_comp,
    UnitaryRep.koopman_apply]
  rw [← h1, ← h2]
  exact UnitaryRep.compMeasurePreserving_congr _ _ _ hfun f

/-! ## C. Symmetry reduction -/

variable [MeasurableSpace (PontryaginDual (Multiplicative G))]
  [BorelSpace (PontryaginDual (Multiplicative G))]

/-- **Symmetry reduction on a crystal.** Let `T` be a bounded operator on `ℓ²` of the sites of a
crystal, commuting with the translations and with the bond-preserving symmetries. Its restriction
to the sector of total momenta in a set `S` of characters is unitarily equivalent to its restriction
to the sector of momenta in the image of `S` under any symmetry, by the symmetry itself. In
particular their spectra agree. -/
lemma spectrum_sectorOp_eq_site {T : SiteSpace G F →L[ℂ] SiteSpace G F}
    (hTπ : ∀ a, Commute ((siteTranslation G F a : unitary _) : SiteSpace G F →L[ℂ] SiteSpace G F) T)
    (hTρ : ∀ s, Commute ((siteSymmetry g s : unitary _) : SiteSpace G F →L[ℂ] SiteSpace G F) T)
    (s : g.symmetries) {S : Set (PontryaginDual (Multiplicative G))} (hS : MeasurableSet S) :
    spectrum ℂ (UnitaryRep.sectorOp hTπ S) =
      spectrum ℂ (UnitaryRep.sectorOp hTπ (UnitaryRep.dualAct (latticeAut g) s '' S)) :=
  UnitaryRep.spectrum_sectorOp_eq (siteTranslation_covariant g) hTπ hTρ s hS

end CondensedMatter
