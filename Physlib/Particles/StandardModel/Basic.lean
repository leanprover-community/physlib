/-
Copyright (c) 2026 Jinzheng Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li
-/
module

public import Physlib.ClassicalFieldTheory.GaugeTheory.LocalGaugeData.OfFactors
public import Physlib.ClassicalFieldTheory.GaugeTheory.MatterField.MatrixRep.Table
/-!
# The Standard Model

## i. Overview

The Standard Model as a model table: the gauge group `SU(3) × SU(2) × U(1)` named by its
factors, each field as its Lorentz label and its charges, and the table assigning each
field its number of generations. Everything else is derived: the local gauge data of the
gauge group is assembled from the factors by `LocalGaugeData.ofFactors`, and the table
compiles, through `Physlib.ClassicalFieldTheory.GaugeTheory.MatterField.MatrixRep.Table`,
to the field content `StandardModel.Model.fieldData : GaugeFieldData gaugeData`, from
which the general theory derives the algebra of field operators and the gauge and Lorentz
actions.

The charges are listed in the order of the factors: the `SU(3)` label, the `SU(2)` label
and the hypercharge. Hypercharges are integers, six times the conventional `Y`, so that
the gauge group acting is the honest `U(1)` of unitary jets. The right-handed singlets are
right-handed Weyl spinors in the fundamental of colour rather than conjugate left-handed
fields.

## ii. Key results

- `StandardModel.Model.gauge` : the gauge group, as a list of factors.
- `StandardModel.Model.gaugeData` : its local gauge data.
- `StandardModel.Model.quarkDoublet`, `leptonDoublet`, `upSinglet`, `downSinglet`,
  `leptonSinglet`, `higgs` : the fields, as their Lorentz label and charges.
- `StandardModel.Model.table` : the table, each field with its number of generations.
- `StandardModel.Model.fieldData` : the field content of the Standard Model.

## iii. Table of contents

- A. The gauge group
- B. The fields
- C. The field content

-/

@[expose] public section

open LocalGaugeData

namespace StandardModel

namespace Model

/-!

## A. The gauge group

-/

/-- The gauge group `SU(3) × SU(2) × U(1)`, as a list of factors. -/
abbrev gauge : List FactorSpec := [.SU 3, .SU 2, .U1]

/-- The local gauge data of the Standard Model gauge group: jets of `SU(3) × SU(2) × U(1)`
  gauge transformations with their Lie algebra of jets. -/
noncomputable abbrev gaugeData := ofFactors gauge

/-- The factors of the gauge group, as what the rows are charged under. -/
noncomputable abbrev factors : Factors gaugeData := Factors.factors gauge

/-!

## B. The fields

Each field is its Lorentz label and its charges in the order of the factors: the `SU(3)`
label, the `SU(2)` label and the hypercharge.

-/

/-- The quark doublet `q ∼ (3, 2)_{1}`. -/
abbrev quarkDoublet : MatterFieldData factors := (.L, .fund, .fund, 1)

/-- The lepton doublet `l ∼ (1, 2)_{-3}`. -/
abbrev leptonDoublet : MatterFieldData factors := (.L, .singlet, .fund, -3)

/-- The up-type quark singlet `u ∼ (3, 1)_{4}`. -/
abbrev upSinglet : MatterFieldData factors := (.R, .fund, .singlet, 4)

/-- The down-type quark singlet `d ∼ (3, 1)_{-2}`. -/
abbrev downSinglet : MatterFieldData factors := (.R, .fund, .singlet, -2)

/-- The charged-lepton singlet `e ∼ (1, 1)_{-6}`. -/
abbrev leptonSinglet : MatterFieldData factors := (.R, .singlet, .singlet, -6)

/-- The Higgs `H ∼ (1, 2)_{3}`. -/
abbrev higgs : MatterFieldData factors := (.scalar, .singlet, .fund, 3)

/-- The fields of the Standard Model. -/
inductive Fields
  /-- The quark doublet. -/
  | q
  /-- The lepton doublet. -/
  | l
  /-- The up-type quark singlet. -/
  | u
  /-- The down-type quark singlet. -/
  | d
  /-- The charged-lepton singlet. -/
  | e
  /-- The Higgs. -/
  | H
  deriving DecidableEq, Repr

instance : Fintype Fields := ⟨{.q, .l, .u, .d, .e, .H}, fun x => by cases x <;> decide⟩

/-!

## C. The field content

-/

/-- **The Standard Model table**: each field with its number of generations, three for the
  fermions and one for the Higgs. -/
def table : FieldData factors Fields
  | .q => (3, quarkDoublet)
  | .l => (3, leptonDoublet)
  | .u => (3, upSinglet)
  | .d => (3, downSinglet)
  | .e => (3, leptonSinglet)
  | .H => (1, higgs)

/-- **The field content of the Standard Model**: the fifteen fermionic species (five fields
  in three generations) and the Higgs, as matter fields of `gaugeData`. -/
noncomputable def fieldData : GaugeFieldData gaugeData := table.toGaugeFieldData

/-- The Standard Model has fifteen fermionic species. -/
lemma card_fermionSpecies : Fintype.card fieldData.FermionSpecies = 15 := by decide

/-- The Standard Model has one bosonic species. -/
lemma card_bosonSpecies : Fintype.card fieldData.BosonSpecies = 1 := by decide

end Model

end StandardModel
