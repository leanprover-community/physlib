/-
Copyright (c) 2026 Nathaneal Sajan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.Mathematics.InvariantReduction
public import PhyslibAlpha.Particles.StandardModel.GaugeGroup.Basic
public import PhyslibAlpha.Relativity.IsLorentzDeriv
/-!
# Invariant reduction for the Standard Model gauge group

The colour and isospin reductions, and stable symbol ranges.

## i. Overview

The Standard Model sectors are classified with `ReducesInvariantsTo` from
`PhyslibAlpha.Mathematics.InvariantReduction`, one index law at a time: colour, isospin and
Lorentz. There the gauge and Lorentz groups are read together as one family,
`gaugeLorentzMaps`, used here with the gauge group `GaugeGroupI`, and a reduction for the gauge
group or the Lorentz group alone transports to it. This file supplies what the sectors share
beyond that. A reduction for the colour factor `SU(3)` or the isospin factor `SU(2)` alone also
transports to the combined family. The range of a symbol map is stable under the gauge group
and, with no derivative slots, under the Lorentz group. That an element fixed by each of the
colour, isospin and hypercharge factors separately is gauge invariant,
`forall_repGauge_eq_self`, is in `GaugeGroup/Basic.lean`.

## ii. Key results

- `ReducesInvariantsTo.ofSU3`, `ReducesInvariantsTo.ofSU2` : a reduction for the colour or
  isospin factor is a reduction for the gauge and Lorentz groups together
- `isStableUnder_range_repGauge`, `isStableUnder_range_repLorentz` : the range of a symbol map
  is stable under the gauge group and, with no derivative slots, under the Lorentz group

## iii. Table of contents

- A. Colour and isospin reductions
- B. Stability of symbol ranges

## iv. References

* None.

-/

@[expose] public section

namespace StandardModel

open TensorProduct Matrix MatrixGroups Lorentz Pointwise ComplexConjugate

/-!

## A. Colour and isospin reductions

The gauge and Lorentz groups are read together as `gaugeLorentzMaps` at `GaugeGroupI`. A
reduction for the colour factor, through `(U, 1, 1)`, or the isospin factor, through
`(1, V, 1)`, is transported to it by `ReducesInvariantsTo.comp`.

-/

section BothGroups

variable {B : Type*} [AddCommGroup B] [Module ℂ B] {repGauge : Representation ℂ GaugeGroupI B}
  {repLorentz : Representation ℂ SL(2,ℂ) B}

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

end BothGroups

/-!

## B. Stability of symbol ranges

The range of a symbol map is carried into itself by the gauge group, and, with no
derivative slots, by the Lorentz group.

-/

section Ranges

variable {B : Type} [Ring B] [Algebra ℂ B]

/-- The range of a symbol map is carried into itself by the gauge group. The symbol is
  equivariant, so a gauge transformation only moves the dual vector it is evaluated at. -/
lemma isStableUnder_range_repGauge {M : Type} [AddCommGroup M] [Module ℂ M]
    {repGauge : Representation ℂ GaugeGroupI B} {ρ : Representation ℂ GaugeGroupI M}
    {F : Module.Dual ℂ M →ₗ[ℂ] B} (hF : ∀ g φ, repGauge g (F φ) = F (ρ.dual g φ)) :
    ∀ g : GaugeGroupI, ∀ y ∈ LinearMap.range F, repGauge g y ∈ LinearMap.range F := by
  rintro g _ ⟨φ, rfl⟩
  exact ⟨ρ.dual g φ, (hF g φ).symm⟩

/-- The range of an underived symbol map is carried into itself by the Lorentz group. With
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
