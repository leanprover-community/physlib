/-
Copyright (c) 2026 Nathaneal Sajan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaneal Sajan
-/
module

public import Physlib.Mathematics.InvariantReduction
public import Physlib.Particles.StandardModel.GaugeGroup.Basic
public import Physlib.Relativity.IsLorentzDeriv
/-!
# Invariant reduction for the gauge and Lorentz groups

The Standard Model sectors are classified with `ReducesInvariantsTo` from
`Physlib.Mathematics.InvariantReduction`, one index law at a time: colour, isospin and Lorentz.
The reductions for the individual laws are `invariantReductionToSpan` beside each
classification theorem. This file supplies what the sectors share when combining them.

- A. The family `gaugeLorentzMaps` indexed by `GaugeGroupI ⊕ SL(2,ℂ)`, the classification
  endpoint for it, the transport of gauge, colour, isospin and Lorentz reductions to it, and
  its multiplicativity.
- B. The colour, isospin and hypercharge factors of a gauge transformation; an element fixed
  by each factor is gauge invariant.
- C. Stability of the range of a symbol map under the gauge and Lorentz groups.
-/

@[expose] public section

namespace StandardModel

open TensorProduct Matrix MatrixGroups Lorentz Pointwise ComplexConjugate

/-!

## A. The gauge and Lorentz groups together

The family indexed by the disjoint union of the two groups has as invariants the elements
fixed by both groups, and as stable submodules those stable under both. A reduction for the
gauge group, its colour or isospin factor, or the Lorentz group is transported to it by
`ReducesInvariantsTo.comp`.

-/

section BothGroups

variable {B : Type*} [AddCommGroup B] [Module ℂ B]
  (repGauge : Representation ℂ GaugeGroupI B)
  (repLorentz : Representation ℂ SL(2,ℂ) B)

/-- The gauge and Lorentz groups read as a single family of linear maps, indexed by their
  disjoint union. -/
def gaugeLorentzMaps : GaugeGroupI ⊕ SL(2,ℂ) → B →ₗ[ℂ] B :=
  Sum.elim (fun g => repGauge g) (fun Λ => repLorentz Λ)

variable {repGauge repLorentz}

/-- A submodule stable under both groups is stable under the combined family, and
  conversely. -/
lemma isStableUnder_gaugeLorentzMaps_iff {V : Submodule ℂ B} :
    IsStableUnder (gaugeLorentzMaps repGauge repLorentz) V
      ↔ (∀ g : GaugeGroupI, ∀ y ∈ V, repGauge g y ∈ V)
        ∧ ∀ Λ : SL(2,ℂ), ∀ y ∈ V, repLorentz Λ y ∈ V := by
  constructor
  · exact fun hV => ⟨fun g => hV (Sum.inl g), fun Λ => hV (Sum.inr Λ)⟩
  · rintro ⟨hg, hL⟩ (g | Λ)
    · exact hg g
    · exact hL Λ

/-- An element fixed by both groups is fixed by the combined family, and conversely. -/
lemma forall_gaugeLorentzMaps_eq_self_iff {x : B} :
    (∀ p, gaugeLorentzMaps repGauge repLorentz p x = x)
      ↔ (∀ g : GaugeGroupI, repGauge g x = x) ∧ ∀ Λ : SL(2,ℂ), repLorentz Λ x = x := by
  constructor
  · exact fun hx => ⟨fun g => hx (Sum.inl g), fun Λ => hx (Sum.inr Λ)⟩
  · rintro ⟨hg, hL⟩ (g | Λ)
    · exact hg g
    · exact hL Λ

/-- A submodule fixed pointwise by both groups is fixed pointwise by the combined family, and
  conversely. -/
lemma isFixedBy_gaugeLorentzMaps_iff {V : Submodule ℂ B} :
    IsFixedBy (gaugeLorentzMaps repGauge repLorentz) V
      ↔ (∀ g : GaugeGroupI, ∀ y ∈ V, repGauge g y = y)
        ∧ ∀ Λ : SL(2,ℂ), ∀ y ∈ V, repLorentz Λ y = y := by
  constructor
  · exact fun hV => ⟨fun g => hV (Sum.inl g), fun Λ => hV (Sum.inr Λ)⟩
  · rintro ⟨hg, hL⟩ (g | Λ)
    · exact hg g
    · exact hL Λ

/-- The classification endpoint `ReducesInvariantsTo.mem_sup_and_forall_eq_self_iff` for the
  gauge and Lorentz groups together, with the two invariances and the two stabilities stated
  separately. -/
lemma ReducesInvariantsTo.mem_sup_and_gauge_lorentz_invariant_iff {V W S : Submodule ℂ B}
    (hP : ReducesInvariantsTo (gaugeLorentzMaps repGauge repLorentz) V W) (hWV : W ≤ V)
    (hW : IsFixedBy (gaugeLorentzMaps repGauge repLorentz) W)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, repGauge g y ∈ S)
    (hSL : ∀ Λ : SL(2,ℂ), ∀ y ∈ S, repLorentz Λ y ∈ S) (x : B) :
    (x ∈ V ⊔ S ∧ (∀ g : GaugeGroupI, repGauge g x = x) ∧ ∀ Λ : SL(2,ℂ), repLorentz Λ x = x)
      ↔ ∃ y ∈ S, (∀ g : GaugeGroupI, repGauge g y = y)
          ∧ (∀ Λ : SL(2,ℂ), repLorentz Λ y = y) ∧ x - y ∈ W := by
  simpa only [forall_gaugeLorentzMaps_eq_self_iff, and_assoc] using
    hP.mem_sup_and_forall_eq_self_iff hWV hW (isStableUnder_gaugeLorentzMaps_iff.2 ⟨hS, hSL⟩) x

/-- A gauge reduction is a reduction for the gauge and Lorentz groups together. -/
lemma ReducesInvariantsTo.ofGauge {V W : Submodule ℂ B}
    (hP : ReducesInvariantsTo (fun g : GaugeGroupI => repGauge g) V W) :
    ReducesInvariantsTo (gaugeLorentzMaps repGauge repLorentz) V W :=
  ReducesInvariantsTo.comp (Sum.inl (β := SL(2,ℂ))) hP

/-- A reduction for the colour factor is a reduction for the gauge and Lorentz groups
  together. -/
lemma ReducesInvariantsTo.ofSU3 {V W : Submodule ℂ B}
    (hP : ReducesInvariantsTo (fun U : specialUnitaryGroup (Fin 3) ℂ => repGauge (U, 1, 1)) V W) :
    ReducesInvariantsTo (gaugeLorentzMaps repGauge repLorentz) V W :=
  ReducesInvariantsTo.comp
    (fun U : specialUnitaryGroup (Fin 3) ℂ => Sum.inl ((U, 1, 1) : GaugeGroupI)) hP

/-- A reduction for the isospin factor is a reduction for the gauge and Lorentz groups
  together. -/
lemma ReducesInvariantsTo.ofSU2 {V W : Submodule ℂ B}
    (hP : ReducesInvariantsTo (fun U : specialUnitaryGroup (Fin 2) ℂ => repGauge (1, U, 1)) V W) :
    ReducesInvariantsTo (gaugeLorentzMaps repGauge repLorentz) V W :=
  ReducesInvariantsTo.comp
    (fun U : specialUnitaryGroup (Fin 2) ℂ => Sum.inl ((1, U, 1) : GaugeGroupI)) hP

/-- A Lorentz reduction is a reduction for the gauge and Lorentz groups together. -/
lemma ReducesInvariantsTo.ofLorentz {V W : Submodule ℂ B}
    (hP : ReducesInvariantsTo (fun Λ : SL(2,ℂ) => repLorentz Λ) V W) :
    ReducesInvariantsTo (gaugeLorentzMaps repGauge repLorentz) V W :=
  ReducesInvariantsTo.comp (Sum.inr (α := GaugeGroupI)) hP

end BothGroups

section Multiplicative

variable {B : Type*} [Ring B] [Algebra ℂ B] {repGauge : Representation ℂ GaugeGroupI B}
  {repLorentz : Representation ℂ SL(2,ℂ) B}

/-- The two groups read as one family of maps respect multiplication, each of the two
  representations doing so. -/
lemma gaugeLorentzMaps_mul
    (hG : ∀ (g : GaugeGroupI) (b₁ b₂ : B),
      repGauge g (b₁ * b₂) = repGauge g b₁ * repGauge g b₂)
    (hL : ∀ (Λ : SL(2,ℂ)) (b₁ b₂ : B),
      repLorentz Λ (b₁ * b₂) = repLorentz Λ b₁ * repLorentz Λ b₂)
    (p : GaugeGroupI ⊕ SL(2,ℂ)) (a b : B) :
    gaugeLorentzMaps repGauge repLorentz p (a * b)
      = gaugeLorentzMaps repGauge repLorentz p a
        * gaugeLorentzMaps repGauge repLorentz p b := by
  cases p with
  | inl g => exact hG g a b
  | inr Λ => exact hL Λ a b

end Multiplicative

/-!

## B. The three factors of a gauge transformation

A gauge transformation is a triple `(U, V, t)`, and the colour, isospin and hypercharge laws
each constrain one factor. This section records the factors and inverses of `(U, 1, 1)`,
`(1, V, 1)` and `(1, 1, t)`, the entries of inverses in `SU(3)` and `SU(2)`, and the
factorisation that turns three separate invariances into gauge invariance.

-/

/-- The entries of the inverse of an `SU(3)` element are the conjugated transposed
  entries, the inverse of a unitary matrix being its conjugate transpose. -/
lemma su3_inv_apply (U : specialUnitaryGroup (Fin 3) ℂ) (a b : Fin 3) :
    (U⁻¹).1 a b = conj (U.1 b a) := by
  rw [← Matrix.star_eq_inv, Matrix.specialUnitaryGroup.coe_star]
  simp [Matrix.star_apply]

/-- The entries of the inverse of an `SU(2)` element are the conjugated transposed
  entries. -/
lemma su2_inv_apply (U : specialUnitaryGroup (Fin 2) ℂ) (a b : Fin 2) :
    (U⁻¹).1 a b = conj (U.1 b a) := by
  rw [← Matrix.star_eq_inv, Matrix.specialUnitaryGroup.coe_star]
  simp [Matrix.star_apply]

/-- The inverse of a unitary scalar is its conjugate. -/
lemma unitary_inv_coe (t : unitary ℂ) : ((t⁻¹ : unitary ℂ) : ℂ) = star (t : ℂ) := rfl

/-- The colour factor of a colour gauge transformation. -/
@[simp] lemma toSU3_su3Elt (U : specialUnitaryGroup (Fin 3) ℂ) :
    GaugeGroupI.toSU3 ((U, 1, 1) : GaugeGroupI) = U := rfl

/-- The isospin factor of a colour gauge transformation is trivial. -/
@[simp] lemma toSU2_su3Elt (U : specialUnitaryGroup (Fin 3) ℂ) :
    GaugeGroupI.toSU2 ((U, 1, 1) : GaugeGroupI) = 1 := rfl

/-- The hypercharge factor of a colour gauge transformation is trivial. -/
@[simp] lemma toU1_su3Elt (U : specialUnitaryGroup (Fin 3) ℂ) :
    GaugeGroupI.toU1 ((U, 1, 1) : GaugeGroupI) = 1 := rfl

/-- The inverse of a colour gauge transformation is the colour transformation of the
  inverse. -/
@[simp] lemma inv_su3Elt (U : specialUnitaryGroup (Fin 3) ℂ) :
    ((U, 1, 1) : GaugeGroupI)⁻¹ = ((U⁻¹, 1, 1) : GaugeGroupI) := by
  simp

/-- The colour factor of an isospin gauge transformation is trivial. -/
@[simp] lemma toSU3_su2Elt (V : specialUnitaryGroup (Fin 2) ℂ) :
    GaugeGroupI.toSU3 ((1, V, 1) : GaugeGroupI) = 1 := rfl

/-- The isospin factor of an isospin gauge transformation. -/
@[simp] lemma toSU2_su2Elt (V : specialUnitaryGroup (Fin 2) ℂ) :
    GaugeGroupI.toSU2 ((1, V, 1) : GaugeGroupI) = V := rfl

/-- The hypercharge factor of an isospin gauge transformation is trivial. -/
@[simp] lemma toU1_su2Elt (V : specialUnitaryGroup (Fin 2) ℂ) :
    GaugeGroupI.toU1 ((1, V, 1) : GaugeGroupI) = 1 := rfl

/-- The inverse of an isospin gauge transformation is the isospin transformation of the
  inverse. -/
@[simp] lemma inv_su2Elt (V : specialUnitaryGroup (Fin 2) ℂ) :
    ((1, V, 1) : GaugeGroupI)⁻¹ = ((1, V⁻¹, 1) : GaugeGroupI) := by
  simp

/-- The colour factor of a hypercharge gauge transformation is trivial. -/
@[simp] lemma toSU3_u1Elt (t : unitary ℂ) :
    GaugeGroupI.toSU3 ((1, 1, t) : GaugeGroupI) = 1 := rfl

/-- The isospin factor of a hypercharge gauge transformation is trivial. -/
@[simp] lemma toSU2_u1Elt (t : unitary ℂ) :
    GaugeGroupI.toSU2 ((1, 1, t) : GaugeGroupI) = 1 := rfl

/-- The hypercharge factor of a hypercharge gauge transformation. -/
@[simp] lemma toU1_u1Elt (t : unitary ℂ) :
    GaugeGroupI.toU1 ((1, 1, t) : GaugeGroupI) = t := rfl

/-- The inverse of a hypercharge gauge transformation is the hypercharge transformation of
  the inverse. -/
@[simp] lemma inv_u1Elt (t : unitary ℂ) :
    ((1, 1, t) : GaugeGroupI)⁻¹ = ((1, 1, t⁻¹) : GaugeGroupI) := by
  simp

/-- A gauge transformation is the product of its colour, isospin and hypercharge parts, so
  an element fixed by each of the three factors separately is gauge invariant. -/
lemma forall_repGauge_eq_self {B : Type*} [AddCommGroup B] [Module ℂ B]
    {rep : Representation ℂ GaugeGroupI B} {x : B}
    (h3 : ∀ U : specialUnitaryGroup (Fin 3) ℂ, rep (U, 1, 1) x = x)
    (h2 : ∀ V : specialUnitaryGroup (Fin 2) ℂ, rep (1, V, 1) x = x)
    (h1 : ∀ t : unitary ℂ, rep (1, 1, t) x = x) (g : GaugeGroupI) : rep g x = x := by
  have hg : g = ((g.1, 1, 1) : GaugeGroupI) * (((1, g.2.1, 1) : GaugeGroupI)
      * ((1, 1, g.2.2) : GaugeGroupI)) := by
    simp [Prod.ext_iff]
  rw [hg, map_mul, Module.End.mul_apply, map_mul, Module.End.mul_apply, h1, h2, h3]

/-!

## C. Stability of symbol ranges

The range of a symbol map is carried into itself by the gauge group, and, with no
derivative slots, by the Lorentz group.

-/

section Ranges

variable {B : Type} [Ring B] [Algebra ℂ B]

/-- The range of a symbol map is carried into itself by the gauge group: the symbol is
  equivariant, so a gauge transformation only moves the dual vector it is evaluated at. -/
lemma isStableUnder_range_repGauge {M : Type} [AddCommGroup M] [Module ℂ M]
    {repGauge : Representation ℂ GaugeGroupI B} {ρ : Representation ℂ GaugeGroupI M}
    {F : Module.Dual ℂ M →ₗ[ℂ] B} (hF : ∀ g φ, repGauge g (F φ) = F (ρ.dual g φ)) :
    ∀ g : GaugeGroupI, ∀ y ∈ LinearMap.range F, repGauge g y ∈ LinearMap.range F := by
  rintro g _ ⟨φ, rfl⟩
  exact ⟨ρ.dual g φ, (hF g φ).symm⟩

/-- The range of an underived symbol map is carried into itself by the Lorentz group: with
  no derivative slots to mix, the transformation law moves the dual vector alone. -/
lemma isStableUnder_range_repLorentz {M : Type} [AddCommGroup M] [Module ℂ M]
    {repLorentz : Representation ℂ SL(2,ℂ) B} {ρ : Representation ℂ SL(2,ℂ) M}
    {F : {n : ℕ} → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ M →ₗ[ℂ] B}
    (hF : IsLorentzCovDerivTransforms repLorentz ρ F) (Λ : SL(2,ℂ)) :
    ∀ y ∈ LinearMap.range (F (![] : Fin 0 → Fin 1 ⊕ Fin 3)),
      repLorentz Λ y ∈ LinearMap.range (F (![] : Fin 0 → Fin 1 ⊕ Fin 3)) := by
  rintro _ ⟨φ, rfl⟩
  rw [hF Λ 0 ![] φ, Fintype.sum_subsingleton _ ![]]
  simp only [Finset.univ_eq_empty, Finset.prod_empty, one_smul]
  exact ⟨ρ.dual Λ φ, rfl⟩

end Ranges

end StandardModel
