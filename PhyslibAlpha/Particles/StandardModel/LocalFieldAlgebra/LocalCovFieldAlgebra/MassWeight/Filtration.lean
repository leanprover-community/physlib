/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.Particles.StandardModel.LocalFieldAlgebra.LocalCovFieldAlgebra.MassWeight.Invariants
/-!
# The mass-weight filtration and the constant term

The gauge and Lorentz invariants of the Standard Model of mass dimension at most four, the
constant term included.

## i. Overview

The grading of the field algebra by mass weight answers one weight at a time. A
Lagrangian is not graded. It is a sum of terms of every weight up to a cut-off, and the
object that holds such a sum is the filtration `massWeightSubmoduleLE w`, the join of the
weight pieces of weight at most `w`.

Passing from the grading to the filtration adds exactly one thing, and it is the thing the
graded statement had to exclude. `Invariants.lean` classifies the invariants of
`massWeightSubmodule w` for `0 < w ≤ 8`, and the lower bound is not an artefact: at weight
zero the field algebra contains the scalars, which are fixed by both groups and lie in no
given `S`, so no classification into a span plus a remainder in `S` can hold there. The
filtration contains weight zero, so the scalars have to be met rather than avoided — and
they are a genuine invariant, the constant term of mass dimension zero, the cosmological
term.

Section B settles what the weight-zero piece is. By the generic
`GaugeFieldData.LocalCovFieldAlgebra.massWeightSubmodule_zero`, every generator carrying positive
weight, `massWeightSubmodule 0` is exactly the scalars, and the unit is fixed by both groups
because both act by algebra maps.

The classification then runs as it does for the grading. `ReducesInvariantsTo` is closed under
joins in its source, and the filtration is a join. Each weight from one to eight reduces to
the Standard-Model span of that weight by `reducesInvariantsTo_massWeightSubmodule`, weight
zero reduces to itself, and the join of the nine is a reduction of the filtration. No independence
of the sectors, and none of the weights, is used anywhere.

The answer at bound eight is spanned by the constant term, the Higgs mass term `H† H`, and
the dimension-four span of `Invariants.lean`, with the same scope: formal expressions,
spanning generators, and no quotient by total derivatives or the equations of motion.

## ii. Key results

- `isStableUnder_massWeightSubmoduleLE` : the filtration is stable under both groups.
- `standardModelSpanLE` : the constant term joined with the Standard-Model span of every weight
  up to `w`.
- `mem_standardModelSpanLE_eight_of_mem_sector` : an invariant element of a sector of mass
  weight at most eight lies in the span of the filtration.
- `mem_massWeightSubmoduleLE_sup_and_gauge_lorentz_invariant_iff` : the classification up to
  mass weight `w ≤ 8`.
- `mem_massWeightSubmoduleLE_eight_sup_and_gauge_lorentz_invariant_iff_lagrangian` : the
  invariant content of the Standard Model up to mass dimension four, written out term by term.

## iii. Table of contents

- A. The mass-weight filtration
- B. The constant term at weight zero
- C. The span of the filtration
- D. Reducing the filtration
- E. The classification up to mass dimension four
- F. The Standard Model Lagrangian with its constant and mass terms

## iv. References

* None.

-/

@[expose] public section

namespace StandardModel

open TensorProduct Matrix MatrixGroups Lorentz

namespace LocalCovFieldAlgebra

open GaugeFieldData.LocalCovFieldAlgebra (massWeightSubmodule_le_massWeightSubmoduleLE
  massWeightComponent massWeightComponent_mem_massWeightSubmodule massWeightComponent_repValue
  massWeightComponent_repLorentzGroup)

/-!

## A. The mass-weight filtration

-/

/-- The filtration is carried into itself by both groups, since each graded piece is. -/
lemma isStableUnder_massWeightSubmoduleLE (w : ℕ) :
    IsStableUnder (gaugeLorentzMaps repGaugeGroupI repLorentzGroup) (massWeightSubmoduleLE w) :=
  isStableUnder_gaugeLorentzMaps_iff.2
    ⟨fun g _ hy => GaugeFieldData.LocalCovFieldAlgebra.repValue_mem_massWeightSubmoduleLE
        isMassWeightPoly (gaugeGroupEquiv g) hy,
      fun Λ _ hy => GaugeFieldData.LocalCovFieldAlgebra.repLorentzGroup_mem_massWeightSubmoduleLE
        isMassWeightPoly fieldData_gaugeLorentzCompatible Λ hy⟩

/-!

## B. The constant term at weight zero

-/

/-- The scalars are fixed by both groups, since each acts by an algebra map, so each fixes the
  unit. This is what makes the constant term an invariant, and it is what the backward
  direction of the classification needs of the weight-zero part of the span. -/
lemma isFixedBy_massWeightSubmodule_zero :
    IsFixedBy (gaugeLorentzMaps repGaugeGroupI repLorentzGroup) (massWeightSubmodule 0) := by
  rw [massWeightSubmodule_zero, Submodule.one_eq_span]
  refine isFixedBy_span_singleton ?_
  rintro (g | Λ)
  · exact repGaugeGroupI_one g
  · exact repLorentzGroup_one Λ

/-!

## C. The span of the filtration

-/

/-- The gauge- and Lorentz-invariant content of the Standard Model up to mass weight `w`. It is
  the weight-zero part of the field algebra, which is the constant term, joined with the
  Standard-Model span of every weight up to `w`. -/
noncomputable def standardModelSpanLE (w : ℕ) : Submodule ℂ fieldData.LocalCovFieldAlgebra :=
  massWeightSubmodule 0 ⊔ ⨆ k ∈ Finset.range (w + 1), standardModelSpan k

/-- The constant term lies in the span of the filtration, at every bound. -/
lemma massWeightSubmodule_zero_le_standardModelSpanLE (w : ℕ) :
    massWeightSubmodule 0 ≤ standardModelSpanLE w := by
  rw [standardModelSpanLE]
  exact le_sup_left

/-- The graded span of a weight at most `w` lies in the span of the filtration at `w`. -/
lemma standardModelSpan_le_standardModelSpanLE {k w : ℕ} (hk : k ≤ w) :
    standardModelSpan k ≤ standardModelSpanLE w := by
  rw [standardModelSpanLE]
  exact le_sup_of_le_right (le_iSup₂_of_le k (Finset.mem_range.2 (Nat.lt_succ_of_le hk)) le_rfl)

/-- The span of the filtration at `w` has mass weight at most `w`. The constant term has
  weight zero and each graded span has its own weight. -/
lemma standardModelSpanLE_le_massWeightSubmoduleLE (w : ℕ) :
    standardModelSpanLE w ≤ massWeightSubmoduleLE w :=
  sup_le (massWeightSubmodule_le_massWeightSubmoduleLE (Nat.zero_le w))
    (iSup₂_le fun k hk => (standardModelSpan_le_massWeightSubmodule k).trans
      (massWeightSubmodule_le_massWeightSubmoduleLE
        (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))))

/-- The span of the filtration is fixed pointwise by the gauge and Lorentz groups
  together. At positive weight this is the fixedness of the graded spans; at weight zero
  it is the fixedness of the unit, and that is the only new content of the filtration. -/
lemma isFixedBy_standardModelSpanLE (w : ℕ) :
    IsFixedBy (gaugeLorentzMaps repGaugeGroupI repLorentzGroup) (standardModelSpanLE w) :=
  isFixedBy_massWeightSubmodule_zero.sup
    (isFixedBy_iSup fun k => isFixedBy_iSup fun _ => isFixedBy_standardModelSpan k)

/-- Every element of the span of the filtration is a gauge invariant. -/
lemma repGauge_of_mem_standardModelSpanLE (w : ℕ) (g : GaugeGroupI)
    {y : fieldData.LocalCovFieldAlgebra}
    (hy : y ∈ standardModelSpanLE w) : repGaugeGroupI g y = y :=
  isFixedBy_standardModelSpanLE w (Sum.inl g) y hy

/-- Every element of the span of the filtration is a Lorentz invariant. -/
lemma repLorentz_of_mem_standardModelSpanLE (w : ℕ) (Λ : SL(2,ℂ))
    {y : fieldData.LocalCovFieldAlgebra}
    (hy : y ∈ standardModelSpanLE w) : repLorentzGroup Λ y = y :=
  isFixedBy_standardModelSpanLE w (Sum.inr Λ) y hy

/-- The span of the filtration at bound eight in reduced form. Of the nine graded spans
  only two are non-trivial, the Higgs mass term at weight four and the dimension-four
  Lagrangian at weight eight, so what survives up to mass dimension four is the constant
  term, the Higgs mass term, and the Lagrangian. -/
lemma standardModelSpanLE_eight :
    standardModelSpanLE 8 = (1 : Submodule ℂ fieldData.LocalCovFieldAlgebra) ⊔
    (ScalarSector.dotSpan 0 0
      ⊔ (GaugeSector.lorentzContractionEightSpan
            ⊔ ScalarSector.lorentzContractionEightSpan
          ⊔ (FermionSector.kineticSpan ⊔ yukawaSpan))) := by
  rw [standardModelSpanLE, massWeightSubmodule_zero, ← standardModelSpan_eight,
    ← standardModelSpan_four]
  congr 1
  refine le_antisymm (iSup₂_le fun k hk => ?_) (sup_le ?_ ?_)
  · rw [Finset.mem_range] at hk
    by_cases hk8 : k = 8
    · subst hk8
      exact le_sup_right
    by_cases hk4 : k = 4
    · subst hk4
      exact le_sup_left
    · rw [standardModelSpan_eq_bot hk8 hk4]
      exact bot_le
  · exact le_iSup₂_of_le 4 (by decide) le_rfl
  · exact le_iSup₂_of_le 8 (by decide) le_rfl

/-!

## D. Reducing the filtration

-/

/-- The filtration reduces to its span, at every bound up to eight. The filtration is a
  join of the graded pieces, each of them stable under both groups, and `ReducesInvariantsTo` is
  closed under joins in its source, so the weights are taken one at a time, each in turn joining the
  error term of the others. At positive weight the graded reduction of `Invariants.lean` is
  used; at weight zero a submodule reduces to itself, the constant term being carried in the
  span. -/
lemma reducesInvariantsTo_massWeightSubmoduleLE {w : ℕ} (hw : w ≤ 8) :
    ReducesInvariantsTo (gaugeLorentzMaps repGaugeGroupI repLorentzGroup) (massWeightSubmoduleLE w)
      (standardModelSpanLE w) := by
  rw [massWeightSubmoduleLE_eq_iSup]
  refine ReducesInvariantsTo.iSup (fun k => ?_) (fun _ => ?_)
    (isFixedBy_standardModelSpanLE w).isStableUnder
  · have hkw : (k : ℕ) ≤ w := Nat.lt_succ_iff.1 k.isLt
    rcases Nat.eq_zero_or_pos (k : ℕ) with hk0 | hk0
    · rw [hk0]
      exact reducesInvariantsTo_of_le (massWeightSubmodule_zero_le_standardModelSpanLE w)
    · exact (reducesInvariantsTo_massWeightSubmodule hk0 (hkw.trans hw)).mono_right
        (standardModelSpan_le_standardModelSpanLE hkw)
  · exact isStableUnder_gaugeLorentzMaps_iff.2
      ⟨fun g _ hy => repGauge_mem_massWeightSubmodule g hy,
        fun Λ _ hy => repLorentz_mem_massWeightSubmodule Λ hy⟩

/-- An element of a sector of mass weight at most eight fixed by both groups lies in the span
  of the filtration at bound eight. Its weight components lie in the weight pieces of the
  sector and are fixed by both groups. The weight-zero component is a constant, and every other
  component lies in the Standard-Model span of its weight by the sector's reduction. -/
lemma mem_standardModelSpanLE_eight_of_mem_sector {A : Finset GaugeFieldData.FieldKind}
    {y : fieldData.LocalCovFieldAlgebra} (hyA : y ∈ fieldData.sector A)
    (hyLE : y ∈ massWeightSubmoduleLE 8)
    (hG : ∀ g : GaugeGroupI, repGaugeGroupI g y = y) (hL : ∀ Λ : SL(2,ℂ), repLorentzGroup Λ y = y) :
    y ∈ standardModelSpanLE 8 := by
  rw [← GaugeFieldData.LocalCovFieldAlgebra.sum_massWeightComponent_of_mem_massWeightSubmoduleLE
    hyLE]
  refine Submodule.sum_mem _ fun k hk => ?_
  have hk8 : k ≤ 8 := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · exact massWeightSubmodule_zero_le_standardModelSpanLE 8
      (massWeightComponent_mem_massWeightSubmodule isMassWeightPoly 0 y)
  have hinvG : ∀ g : GaugeGroupI, repGaugeGroupI g (massWeightComponent massWeightPoly k y)
      = massWeightComponent massWeightPoly k y :=
    fun g => (massWeightComponent_repValue isMassWeightPoly (gaugeGroupEquiv g) k y).symm.trans
      (congrArg (massWeightComponent massWeightPoly k) (hG g))
  have hinvL : ∀ Λ : SL(2,ℂ), repLorentzGroup Λ (massWeightComponent massWeightPoly k y)
      = massWeightComponent massWeightPoly k y :=
    fun Λ => (massWeightComponent_repLorentzGroup isMassWeightPoly
      fieldData_gaugeLorentzCompatible Λ k y).symm.trans
        (congrArg (massWeightComponent massWeightPoly k) (hL Λ))
  have h := reducesInvariantsTo_sectorMassWeight hk0 hk8 A ⊥ isStableUnder_bot _
    (Submodule.mem_sup_left (GaugeFieldData.massWeightComponent_mem_sectorMassWeight
      isMassWeightPoly hyA k)) (forall_gaugeLorentzMaps_eq_self_iff.2 ⟨hinvG, hinvL⟩)
  rw [sup_bot_eq] at h
  exact standardModelSpan_le_standardModelSpanLE hk8 h

/-!

## E. The classification up to mass dimension four

-/

/-- The classification of the Standard Model up to mass weight `w ≤ 8` as an equivalence,
  in the shape every sector uses. An element of `massWeightSubmoduleLE w ⊔ S`, with `S`
  stable under both groups, is fixed by both groups exactly when it is a combination of
  the constant term and the Standard-Model terms of weight at most `w`, up to a remainder
  in `S` fixed by both groups. -/
lemma mem_massWeightSubmoduleLE_sup_and_gauge_lorentz_invariant_iff (w : ℕ) (hw : w ≤ 8)
    (S : Submodule ℂ fieldData.LocalCovFieldAlgebra)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, repGaugeGroupI g y ∈ S)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentzGroup g y ∈ S) (x : fieldData.LocalCovFieldAlgebra) :
    (x ∈ massWeightSubmoduleLE w ⊔ S ∧ (∀ g : GaugeGroupI, repGaugeGroupI g x = x)
        ∧ ∀ g : SL(2,ℂ), repLorentzGroup g x = x)
      ↔ ∃ y ∈ S, (∀ g : GaugeGroupI, repGaugeGroupI g y = y)
          ∧ (∀ g : SL(2,ℂ), repLorentzGroup g y = y)
          ∧ x - y ∈ standardModelSpanLE w :=
  ReducesInvariantsTo.mem_sup_and_gauge_lorentz_invariant_iff
    (reducesInvariantsTo_massWeightSubmoduleLE hw)
    (standardModelSpanLE_le_massWeightSubmoduleLE w) (isFixedBy_standardModelSpanLE w) hS
    hSL x

/-- The gauge and Lorentz invariants of mass weight at most `w`, for `w ≤ 8`, modulo a
  submodule `S` stable under both groups. Such an invariant is a combination of the
  constant term and the Standard-Model terms of weight at most `w`, plus a remainder in
  `S`, and the remainder is fixed by both groups as well, being the difference of two
  invariants. -/
lemma exists_mem_standardModelSpanLE_of_gauge_and_lorentz_invariant (w : ℕ) (hw : w ≤ 8)
    (S : Submodule ℂ fieldData.LocalCovFieldAlgebra)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, repGaugeGroupI g y ∈ S)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentzGroup g y ∈ S) {x : fieldData.LocalCovFieldAlgebra}
    (hx : x ∈ massWeightSubmoduleLE w ⊔ S)
    (hG : ∀ g : GaugeGroupI, repGaugeGroupI g x = x)
    (hL : ∀ g : SL(2,ℂ), repLorentzGroup g x = x) :
    ∃ y ∈ S, (∀ g : GaugeGroupI, repGaugeGroupI g y = y)
      ∧ (∀ g : SL(2,ℂ), repLorentzGroup g y = y)
      ∧ x - y ∈ standardModelSpanLE w :=
  (mem_massWeightSubmoduleLE_sup_and_gauge_lorentz_invariant_iff w hw S hS hSL x).1
    ⟨hx, hG, hL⟩

/-- The same classification without the existential. At every bound up to eight an element
  of `massWeightSubmoduleLE w ⊔ S` fixed by both groups is an element of the span of the
  filtration joined with `S` fixed by both groups, and conversely. -/
lemma mem_massWeightSubmoduleLE_sup_and_gauge_lorentz_invariant_iff_mem (w : ℕ)
    (hw : w ≤ 8) (S : Submodule ℂ fieldData.LocalCovFieldAlgebra)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, repGaugeGroupI g y ∈ S)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentzGroup g y ∈ S) (x : fieldData.LocalCovFieldAlgebra) :
    (x ∈ massWeightSubmoduleLE w ⊔ S ∧ (∀ g : GaugeGroupI, repGaugeGroupI g x = x)
        ∧ ∀ g : SL(2,ℂ), repLorentzGroup g x = x)
      ↔ (x ∈ standardModelSpanLE w ⊔ S ∧ (∀ g : GaugeGroupI, repGaugeGroupI g x = x)
          ∧ ∀ g : SL(2,ℂ), repLorentzGroup g x = x) :=
  ⟨fun hx => ⟨reducesInvariantsTo_massWeightSubmoduleLE hw S
      (isStableUnder_gaugeLorentzMaps_iff.2 ⟨hS, hSL⟩) x hx.1
      (forall_gaugeLorentzMaps_eq_self_iff.2 hx.2), hx.2⟩,
    fun hx => ⟨sup_le_sup_right (standardModelSpanLE_le_massWeightSubmoduleLE w) S hx.1,
      hx.2⟩⟩

/-!

## F. The Standard Model Lagrangian with its constant and mass terms

-/

/-- The classification at bound eight, that is at mass dimension at most four, as an
  equivalence. An element of `massWeightSubmoduleLE 8 ⊔ S`, with `S` stable under both
  groups, is fixed by both groups exactly when it lies in the span of the filtration up to
  a remainder in `S` fixed by both groups. -/
lemma mem_massWeightSubmoduleLE_eight_sup_and_gauge_lorentz_invariant_iff
    (S : Submodule ℂ fieldData.LocalCovFieldAlgebra)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, repGaugeGroupI g y ∈ S)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentzGroup g y ∈ S) (x : fieldData.LocalCovFieldAlgebra) :
    (x ∈ massWeightSubmoduleLE 8 ⊔ S ∧ (∀ g : GaugeGroupI, repGaugeGroupI g x = x)
        ∧ ∀ g : SL(2,ℂ), repLorentzGroup g x = x)
      ↔ ∃ y ∈ S, (∀ g : GaugeGroupI, repGaugeGroupI g y = y)
          ∧ (∀ g : SL(2,ℂ), repLorentzGroup g y = y)
          ∧ x - y ∈ standardModelSpanLE 8 :=
  mem_massWeightSubmoduleLE_sup_and_gauge_lorentz_invariant_iff 8 le_rfl S hS hSL x

/-- The same at bound eight without the existential. -/
lemma mem_massWeightSubmoduleLE_eight_sup_and_gauge_lorentz_invariant_iff_mem
    (S : Submodule ℂ fieldData.LocalCovFieldAlgebra)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, repGaugeGroupI g y ∈ S)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentzGroup g y ∈ S) (x : fieldData.LocalCovFieldAlgebra) :
    (x ∈ massWeightSubmoduleLE 8 ⊔ S ∧ (∀ g : GaugeGroupI, repGaugeGroupI g x = x)
        ∧ ∀ g : SL(2,ℂ), repLorentzGroup g x = x)
      ↔ (x ∈ standardModelSpanLE 8 ⊔ S ∧ (∀ g : GaugeGroupI, repGaugeGroupI g x = x)
          ∧ ∀ g : SL(2,ℂ), repLorentzGroup g x = x) :=
  mem_massWeightSubmoduleLE_sup_and_gauge_lorentz_invariant_iff_mem 8 le_rfl S hS hSL x

/-- The invariant content of the Standard Model up to mass dimension four. An element of
  `massWeightSubmoduleLE 8 ⊔ S`, for `S` a submodule stable under both groups, is fixed by
  the gauge group and the Lorentz group exactly when it is a combination of
  the constant term, of mass dimension zero,
  the Higgs mass term `H† H`, of mass dimension two (`ScalarSector.dotSpan`),
  and the dimension-four span — the four Lorentz contractions of the three `F·F` trace
  families and of the twice-derived hypercharge field strength, among them the gauge
  kinetic and theta terms (`GaugeSector.lorentzContractionEightSpan`), the Higgs
  kinetic term, its quartic potential and its two box terms
  (`ScalarSector.lorentzContractionEightSpan`), the kinetic terms of the ten fermion
  species over the nine family pairs (`FermionSector.kineticSpan`), and the six Yukawa
  couplings over the nine family pairs (`yukawaSpan`) —
  up to a remainder in `S` fixed by both groups, and nothing else. The generators span;
  they are not shown to be independent, and no quotient by total derivatives is taken. -/
lemma mem_massWeightSubmoduleLE_eight_sup_and_gauge_lorentz_invariant_iff_lagrangian
    (S : Submodule ℂ fieldData.LocalCovFieldAlgebra)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, repGaugeGroupI g y ∈ S)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentzGroup g y ∈ S) (x : fieldData.LocalCovFieldAlgebra) :
    (x ∈ massWeightSubmoduleLE 8 ⊔ S ∧ (∀ g : GaugeGroupI, repGaugeGroupI g x = x)
        ∧ ∀ g : SL(2,ℂ), repLorentzGroup g x = x)
      ↔ ∃ y ∈ S, (∀ g : GaugeGroupI, repGaugeGroupI g y = y)
          ∧ (∀ g : SL(2,ℂ), repLorentzGroup g y = y)
          ∧ x - y ∈ (1 : Submodule ℂ fieldData.LocalCovFieldAlgebra) ⊔ (ScalarSector.dotSpan 0 0
              ⊔ (GaugeSector.lorentzContractionEightSpan
                    ⊔ ScalarSector.lorentzContractionEightSpan
                  ⊔ (FermionSector.kineticSpan ⊔ yukawaSpan))) := by
  rw [← standardModelSpanLE_eight]
  exact mem_massWeightSubmoduleLE_eight_sup_and_gauge_lorentz_invariant_iff S hS hSL x

end LocalCovFieldAlgebra

end StandardModel
