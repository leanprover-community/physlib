/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.Particles.StandardModel.LocalFieldAlgebra.YukawaSector.Families.BarHiggs
public import PhyslibAlpha.Particles.StandardModel.LocalFieldAlgebra.YukawaSector.GaugeWeight
public import PhyslibAlpha.Relativity.Tensors.ComplexTensor.Metrics.Basic
/-!
# The Yukawa sector at mass weight eight

The gauge- and Lorentz-invariant Yukawa terms of the Standard Model's covariant field algebra.

## i. Overview

Everything below is stated about the covariant field algebra `fieldData.LocalCovFieldAlgebra` of the
Standard Model.

This is the theorem the Yukawa sector exists for.  At mass weight eight the sector is one
Higgs tower against two underived fermion towers, and the claim proved here is that its
gauge- and Lorentz-invariant content, modulo a submodule `S` stable under both groups, is
exactly the span of the six Yukawa couplings over the nine family pairs.  Nothing else
survives, neither a fourth coupling, nor extra colour or isospin structure inside a surviving
block, nor an invariant carrying a free spinor index.

Three things are already done and are used as given.  Hypercharge has sieved the two
hundred blocks of the gauge weight decomposition down to twelve, in
`sectorMassWeightEightGaugeWeight_piece_zero`.  A gauge invariant of the sector lies in
that weight-zero piece modulo `S`, by `mem_sectorMassWeightEight_piece_zero_sup_of_invariant`.
And the six couplings, their index laws and their contractions are built in the `Families`
files, together with `yukawaSpan_le_inf`, which is the easy direction of the equivalence.

What is left is the reduction.  A block of the decomposition is a product of three symbol
ranges, and the classification of its invariants is three classifications in a row —
colour, then isospin, then Lorentz — each cutting the span down to the span of one
contraction.  The three groups are different, and the fifty-four surviving blocks have to
be reduced one at a time, so the argument is organised around a single relation
`ReducesInvariantsTo σ V W`, saying that a `σ`-invariant of `V ⊔ S` lies in `W ⊔ S` whenever `S` is
`σ`-stable. That relation composes, being transitive, antitone in its source, monotone in its
target, and closed under joins of stable sources, and each `GaugeGroup` or `LorentzGroup`
classification used here is an instance of it, packaged as an `InvariantReductionToSpan`.

## ii. Key results

- `sectorMassWeightEightGaugeWeight_piece_zero_le` : the weight-zero piece inside the six
  surviving block submodules.
- `reducesInvariantsTo_yukawaSpan` : the six blocks, over the nine family pairs, reduce to the
  Yukawa span.
- `reducesInvariantsTo_sectorMassWeight_higgs_fermion_eight` : the sector at mass weight
  eight reduces to the Yukawa span.
- `mem_sectorMassWeight_higgs_fermion_eight_sup_and_gauge_lorentz_invariant_iff` : the
  classification as an equivalence, in the form the sibling sectors state it in.

## iii. Table of contents

- A. The symbol ranges as spans of components
- B. The block submodules and their stability
- C. The twelve surviving blocks as six submodules
- D. The blocks reduce to the Yukawa terms
- E. The classification of the invariants of mass weight eight

## iv. References

* None.

-/

@[expose] public section

open TensorSpecies

namespace StandardModel

open GaugeFieldData (FieldKind)

open TensorProduct Matrix MatrixGroups Lorentz Pointwise ComplexConjugate

namespace LocalCovFieldAlgebra

/-!

## A. The symbol ranges as spans of components

-/

/-- The Higgs submodule without derivatives lies in the span of the Higgs components. -/
lemma higgsSubmodule_zero_le :
    ScalarSector.higgsSubmodule 0
      ≤ Submodule.span ℂ (Set.range (ScalarSector.higgs ![])) := by
  refine iSup_le fun l => ?_
  rw [show l = (![] : Fin 0 → Fin 1 ⊕ Fin 3) from Subsingleton.elim _ _,
    LinearMap.range_eq_span_range_basis HiggsVec.orthonormBasis.toBasis.dualBasis
      (ScalarSector.covH 0 ![])]
  exact le_rfl

/-- The conjugate Higgs submodule without derivatives lies in the span of the conjugate
  Higgs components. -/
lemma barHiggsSubmodule_zero_le :
    ScalarSector.barHiggsSubmodule 0
      ≤ Submodule.span ℂ (Set.range (ScalarSector.barHiggs ![])) := by
  refine iSup_le fun l => ?_
  rw [show l = (![] : Fin 0 → Fin 1 ⊕ Fin 3) from Subsingleton.elim _ _,
    LinearMap.range_eq_span_range_basis (Basis.conj HiggsVec.orthonormBasis.toBasis).dualBasis
      (ScalarSector.covBarH 0 ![])]
  exact le_rfl

/-- The range of the down-singlet symbol map is the span of its components. -/
lemma range_d_eq (f : Fin 3) :
    LinearMap.range (downSingletField f (![] : Fin 0 → Fin 1 ⊕ Fin 3))
      = Submodule.span ℂ (Set.range (FermionSector.dComponent f ![])) :=
  LinearMap.range_eq_span_range_basis DownSinglet.basis.dualBasis (downSingletField f
    ![])

/-- The range of the conjugate down-singlet symbol map is the span of its components. -/
lemma range_bard_eq (f : Fin 3) :
    LinearMap.range (conjDownSingletField f (![] : Fin 0 → Fin 1 ⊕ Fin 3))
      = Submodule.span ℂ (Set.range (FermionSector.bardComponent f ![])) :=
  LinearMap.range_eq_span_range_basis (Basis.conj DownSinglet.basis).dualBasis
    (conjDownSingletField f ![])

/-- The range of the up-singlet symbol map is the span of its components. -/
lemma range_u_eq (f : Fin 3) :
    LinearMap.range (upSingletField f (![] : Fin 0 → Fin 1 ⊕ Fin 3))
      = Submodule.span ℂ (Set.range (FermionSector.uComponent f ![])) :=
  LinearMap.range_eq_span_range_basis UpSinglet.basis.dualBasis (upSingletField f ![])

/-- The range of the conjugate up-singlet symbol map is the span of its components. -/
lemma range_baru_eq (f : Fin 3) :
    LinearMap.range (conjUpSingletField f (![] : Fin 0 → Fin 1 ⊕ Fin 3))
      = Submodule.span ℂ (Set.range (FermionSector.baruComponent f ![])) :=
  LinearMap.range_eq_span_range_basis (Basis.conj UpSinglet.basis).dualBasis
    (conjUpSingletField f ![])

/-- The range of the quark-doublet symbol map is the span of its components. -/
lemma range_Q_eq (f : Fin 3) :
    LinearMap.range (quarkDoubletField f (![] : Fin 0 → Fin 1 ⊕ Fin 3))
      = Submodule.span ℂ (Set.range (FermionSector.QComponent f ![])) :=
  LinearMap.range_eq_span_range_basis QuarkDoublet.basis.dualBasis (quarkDoubletField
    f ![])

/-- The range of the conjugate quark-doublet symbol map is the span of its components. -/
lemma range_barQ_eq (f : Fin 3) :
    LinearMap.range (conjQuarkDoubletField f (![] : Fin 0 → Fin 1 ⊕ Fin 3))
      = Submodule.span ℂ (Set.range (FermionSector.barQComponent f ![])) :=
  LinearMap.range_eq_span_range_basis (Basis.conj QuarkDoublet.basis).dualBasis
    (conjQuarkDoubletField f ![])

/-- The range of the lepton-doublet symbol map is the span of its components. -/
lemma range_L_eq (f : Fin 3) :
    LinearMap.range (leptonDoubletField f (![] : Fin 0 → Fin 1 ⊕ Fin 3))
      = Submodule.span ℂ (Set.range (FermionSector.LComponent f ![])) :=
  LinearMap.range_eq_span_range_basis LeptonDoubletV.basis.dualBasis
    (leptonDoubletField f ![])

/-- The range of the conjugate lepton-doublet symbol map is the span of its components. -/
lemma range_barL_eq (f : Fin 3) :
    LinearMap.range (conjLeptonDoubletField f (![] : Fin 0 → Fin 1 ⊕ Fin 3))
      = Submodule.span ℂ (Set.range (FermionSector.barLComponent f ![])) :=
  LinearMap.range_eq_span_range_basis (Basis.conj LeptonDoubletV.basis).dualBasis
    (conjLeptonDoubletField f ![])

/-- The range of the lepton-singlet symbol map is the span of its components. -/
lemma range_e_eq (f : Fin 3) :
    LinearMap.range (leptonSingletField f (![] : Fin 0 → Fin 1 ⊕ Fin 3))
      = Submodule.span ℂ (Set.range (FermionSector.eComponent f ![])) :=
  LinearMap.range_eq_span_range_basis LeptonSinglet.basis.dualBasis
    (leptonSingletField f ![])

/-- The range of the conjugate lepton-singlet symbol map is the span of its components. -/
lemma range_bare_eq (f : Fin 3) :
    LinearMap.range (conjLeptonSingletField f (![] : Fin 0 → Fin 1 ⊕ Fin 3))
      = Submodule.span ℂ (Set.range (FermionSector.bareComponent f ![])) :=
  LinearMap.range_eq_span_range_basis (Basis.conj LeptonSinglet.basis).dualBasis
    (conjLeptonSingletField f ![])

/-!

## B. The block submodules and their stability

A surviving block of the decomposition is the product of a Higgs range with two fermion
ranges, and this is the submodule the classification of that block runs inside.  All six
are carried into themselves by both groups, each factor being the range of an equivariant
symbol map with no derivative slots for the Lorentz group to mix, and a product of stable
submodules being stable.  That stability is what lets the six blocks — fifty-four of them
once the family pairs are counted — be reduced one at a time, each in turn joining the
error term of the others.

-/

/-- The Higgs submodule without derivatives is carried into itself by both groups. -/
lemma isStableUnder_higgsSubmodule_zero :
    IsStableUnder (gaugeLorentzMaps repGaugeGroupI repLorentzGroup)
      (ScalarSector.higgsSubmodule 0) := by
  refine isStableUnder_iSup fun l => isStableUnder_gaugeLorentzMaps_iff.2 ⟨?_, fun Λ => ?_⟩
  · exact isStableUnder_range_repGauge fun g φ => ScalarSector.H_equivariant g φ 0 l
  · rw [show l = (![] : Fin 0 → Fin 1 ⊕ Fin 3) from Subsingleton.elim _ _]
    exact isStableUnder_range_repLorentz ScalarSector.repLorentz_H Λ

/-- The conjugate Higgs submodule without derivatives is carried into itself by both
  groups. -/
lemma isStableUnder_barHiggsSubmodule_zero :
    IsStableUnder (gaugeLorentzMaps repGaugeGroupI repLorentzGroup)
      (ScalarSector.barHiggsSubmodule 0) := by
  refine isStableUnder_iSup fun l => isStableUnder_gaugeLorentzMaps_iff.2 ⟨?_, fun Λ => ?_⟩
  · exact isStableUnder_range_repGauge fun g φ => ScalarSector.barH_equivariant g φ 0 l
  · rw [show l = (![] : Fin 0 → Fin 1 ⊕ Fin 3) from Subsingleton.elim _ _]
    exact isStableUnder_range_repLorentz ScalarSector.repLorentz_barH Λ

/-- The range of the down-singlet symbol map is carried into itself by both groups. -/
lemma isStableUnder_range_d (f : Fin 3) :
    IsStableUnder (gaugeLorentzMaps repGaugeGroupI repLorentzGroup)
      (LinearMap.range (downSingletField f (![] : Fin 0 → Fin 1 ⊕ Fin 3))) :=
  isStableUnder_gaugeLorentzMaps_iff.2
    ⟨isStableUnder_range_repGauge fun g φ => FermionSector.repGauge_d g f ![] φ,
      fun Λ => isStableUnder_range_repLorentz (FermionSector.repLorentz_d f) Λ⟩

/-- The range of the conjugate down-singlet symbol map is carried into itself by both
  groups. -/
lemma isStableUnder_range_bard (f : Fin 3) :
    IsStableUnder (gaugeLorentzMaps repGaugeGroupI repLorentzGroup)
      (LinearMap.range (conjDownSingletField f (![] : Fin 0 → Fin 1 ⊕ Fin 3))) :=
  isStableUnder_gaugeLorentzMaps_iff.2
    ⟨isStableUnder_range_repGauge fun g φ => FermionSector.repGauge_bard g f ![] φ,
      fun Λ => isStableUnder_range_repLorentz (FermionSector.repLorentz_bard f) Λ⟩

/-- The range of the up-singlet symbol map is carried into itself by both groups. -/
lemma isStableUnder_range_u (f : Fin 3) :
    IsStableUnder (gaugeLorentzMaps repGaugeGroupI repLorentzGroup)
      (LinearMap.range (upSingletField f (![] : Fin 0 → Fin 1 ⊕ Fin 3))) :=
  isStableUnder_gaugeLorentzMaps_iff.2
    ⟨isStableUnder_range_repGauge fun g φ => FermionSector.repGauge_u g f ![] φ,
      fun Λ => isStableUnder_range_repLorentz (FermionSector.repLorentz_u f) Λ⟩

/-- The range of the conjugate up-singlet symbol map is carried into itself by both
  groups. -/
lemma isStableUnder_range_baru (f : Fin 3) :
    IsStableUnder (gaugeLorentzMaps repGaugeGroupI repLorentzGroup)
      (LinearMap.range (conjUpSingletField f (![] : Fin 0 → Fin 1 ⊕ Fin 3))) :=
  isStableUnder_gaugeLorentzMaps_iff.2
    ⟨isStableUnder_range_repGauge fun g φ => FermionSector.repGauge_baru g f ![] φ,
      fun Λ => isStableUnder_range_repLorentz (FermionSector.repLorentz_baru f) Λ⟩

/-- The range of the quark-doublet symbol map is carried into itself by both groups. -/
lemma isStableUnder_range_Q (f : Fin 3) :
    IsStableUnder (gaugeLorentzMaps repGaugeGroupI repLorentzGroup)
      (LinearMap.range (quarkDoubletField f (![] : Fin 0 → Fin 1 ⊕ Fin 3))) :=
  isStableUnder_gaugeLorentzMaps_iff.2
    ⟨isStableUnder_range_repGauge fun g φ => FermionSector.repGauge_Q g f ![] φ,
      fun Λ => isStableUnder_range_repLorentz (FermionSector.repLorentz_Q f) Λ⟩

/-- The range of the conjugate quark-doublet symbol map is carried into itself by both
  groups. -/
lemma isStableUnder_range_barQ (f : Fin 3) :
    IsStableUnder (gaugeLorentzMaps repGaugeGroupI repLorentzGroup)
      (LinearMap.range (conjQuarkDoubletField f (![] : Fin 0 → Fin 1 ⊕ Fin 3))) :=
  isStableUnder_gaugeLorentzMaps_iff.2
    ⟨isStableUnder_range_repGauge fun g φ => FermionSector.repGauge_barQ g f ![] φ,
      fun Λ => isStableUnder_range_repLorentz (FermionSector.repLorentz_barQ f) Λ⟩

/-- The range of the lepton-doublet symbol map is carried into itself by both groups. -/
lemma isStableUnder_range_L (f : Fin 3) :
    IsStableUnder (gaugeLorentzMaps repGaugeGroupI repLorentzGroup)
      (LinearMap.range (leptonDoubletField f (![] : Fin 0 → Fin 1 ⊕ Fin 3))) :=
  isStableUnder_gaugeLorentzMaps_iff.2
    ⟨isStableUnder_range_repGauge fun g φ => FermionSector.repGauge_L g f ![] φ,
      fun Λ => isStableUnder_range_repLorentz (FermionSector.repLorentz_L f) Λ⟩

/-- The range of the conjugate lepton-doublet symbol map is carried into itself by both
  groups. -/
lemma isStableUnder_range_barL (f : Fin 3) :
    IsStableUnder (gaugeLorentzMaps repGaugeGroupI repLorentzGroup)
      (LinearMap.range (conjLeptonDoubletField f (![] : Fin 0 → Fin 1 ⊕ Fin 3))) :=
  isStableUnder_gaugeLorentzMaps_iff.2
    ⟨isStableUnder_range_repGauge fun g φ => FermionSector.repGauge_barL g f ![] φ,
      fun Λ => isStableUnder_range_repLorentz (FermionSector.repLorentz_barL f) Λ⟩

/-- The range of the lepton-singlet symbol map is carried into itself by both groups. -/
lemma isStableUnder_range_e (f : Fin 3) :
    IsStableUnder (gaugeLorentzMaps repGaugeGroupI repLorentzGroup)
      (LinearMap.range (leptonSingletField f (![] : Fin 0 → Fin 1 ⊕ Fin 3))) :=
  isStableUnder_gaugeLorentzMaps_iff.2
    ⟨isStableUnder_range_repGauge fun g φ => FermionSector.repGauge_e g f ![] φ,
      fun Λ => isStableUnder_range_repLorentz (FermionSector.repLorentz_e f) Λ⟩

/-- The range of the conjugate lepton-singlet symbol map is carried into itself by both
  groups. -/
lemma isStableUnder_range_bare (f : Fin 3) :
    IsStableUnder (gaugeLorentzMaps repGaugeGroupI repLorentzGroup)
      (LinearMap.range (conjLeptonSingletField f (![] : Fin 0 → Fin 1 ⊕ Fin 3))) :=
  isStableUnder_gaugeLorentzMaps_iff.2
    ⟨isStableUnder_range_repGauge fun g φ => FermionSector.repGauge_bare g f ![] φ,
      fun Λ => isStableUnder_range_repLorentz (FermionSector.repLorentz_bare f) Λ⟩

/-!

## C. The twelve surviving blocks as six submodules

The twelve blocks that hypercharge leaves come in six transposed pairs, and a pair is one
submodule: the two fermion factors commute as submodules, by `mul_comm_of_le_derivSubmodule`,
so exchanging them changes nothing.  Under the join over family pairs the transposed block
of `(f, f')` is the untransposed block of `(f', f)`, and the weight-zero piece of the sector
lands inside the join of the six.

-/

/-- The submodule of the down-type block `H d barQ` of a family pair. -/
noncomputable def downBlockSubmodule (f f' : Fin 3) : Submodule ℂ fieldData.LocalCovFieldAlgebra :=
  ScalarSector.higgsSubmodule 0 *
    (LinearMap.range (downSingletField f (![] : Fin 0 → Fin 1 ⊕ Fin 3))
    * LinearMap.range (conjQuarkDoubletField f' (![] : Fin 0 → Fin 1 ⊕ Fin 3)))

/-- The submodule of the up-type block `H baru Q` of a family pair. -/
noncomputable def upBlockSubmodule (f f' : Fin 3) : Submodule ℂ fieldData.LocalCovFieldAlgebra :=
  ScalarSector.higgsSubmodule 0 *
    (LinearMap.range (conjUpSingletField f (![] : Fin 0 → Fin 1 ⊕ Fin 3))
    * LinearMap.range (quarkDoubletField f' (![] : Fin 0 → Fin 1 ⊕ Fin 3)))

/-- The submodule of the charged-lepton block `H barL e` of a family pair. -/
noncomputable def leptonBlockSubmodule (f f' : Fin 3) : Submodule ℂ
    fieldData.LocalCovFieldAlgebra :=
  ScalarSector.higgsSubmodule 0 *
    (LinearMap.range (conjLeptonDoubletField f (![] : Fin 0 → Fin 1 ⊕ Fin 3))
    * LinearMap.range (leptonSingletField f' (![] : Fin 0 → Fin 1 ⊕ Fin 3)))

/-- The submodule of the conjugate down-type block `barH bard Q` of a family pair. -/
noncomputable def barDownBlockSubmodule (f f' : Fin 3) : Submodule ℂ
    fieldData.LocalCovFieldAlgebra :=
  ScalarSector.barHiggsSubmodule 0
    * (LinearMap.range (conjDownSingletField f (![] : Fin 0 → Fin 1 ⊕ Fin 3))
      * LinearMap.range (quarkDoubletField f' (![] : Fin 0 → Fin 1 ⊕ Fin 3)))

/-- The submodule of the conjugate up-type block `barH u barQ` of a family pair. -/
noncomputable def barUpBlockSubmodule (f f' : Fin 3) : Submodule ℂ fieldData.LocalCovFieldAlgebra :=
  ScalarSector.barHiggsSubmodule 0
    * (LinearMap.range (upSingletField f (![] : Fin 0 → Fin 1 ⊕ Fin 3))
      * LinearMap.range (conjQuarkDoubletField f' (![] : Fin 0 → Fin 1 ⊕ Fin 3)))

/-- The submodule of the conjugate charged-lepton block `barH L bare` of a family pair. -/
noncomputable def barLeptonBlockSubmodule
    (f f' : Fin 3) : Submodule ℂ fieldData.LocalCovFieldAlgebra :=
  ScalarSector.barHiggsSubmodule 0
    * (LinearMap.range (leptonDoubletField f (![] : Fin 0 → Fin 1 ⊕ Fin 3))
      * LinearMap.range (conjLeptonSingletField f' (![] : Fin 0 → Fin 1 ⊕ Fin 3)))

/-- The down-type block submodule is carried into itself by both groups. -/
lemma isStableUnder_downBlockSubmodule (f f' : Fin 3) :
    IsStableUnder (gaugeLorentzMaps repGaugeGroupI repLorentzGroup)
      (LocalCovFieldAlgebra.downBlockSubmodule f f') :=
  IsStableUnder.mul (gaugeLorentzMaps_mul repGaugeGroupI_mul
    repLorentzGroup_mul)
    LocalCovFieldAlgebra.isStableUnder_higgsSubmodule_zero
    (IsStableUnder.mul (gaugeLorentzMaps_mul repGaugeGroupI_mul
      repLorentzGroup_mul)
      (LocalCovFieldAlgebra.isStableUnder_range_d f) (LocalCovFieldAlgebra.isStableUnder_range_barQ
        f'))

/-- The up-type block submodule is carried into itself by both groups. -/
lemma isStableUnder_upBlockSubmodule (f f' : Fin 3) :
    IsStableUnder (gaugeLorentzMaps repGaugeGroupI repLorentzGroup)
      (LocalCovFieldAlgebra.upBlockSubmodule f f') :=
  IsStableUnder.mul (gaugeLorentzMaps_mul repGaugeGroupI_mul
    repLorentzGroup_mul)
    LocalCovFieldAlgebra.isStableUnder_higgsSubmodule_zero
    (IsStableUnder.mul (gaugeLorentzMaps_mul repGaugeGroupI_mul
      repLorentzGroup_mul)
      (LocalCovFieldAlgebra.isStableUnder_range_baru f) (LocalCovFieldAlgebra.isStableUnder_range_Q
        f'))

/-- The charged-lepton block submodule is carried into itself by both groups. -/
lemma isStableUnder_leptonBlockSubmodule (f f' : Fin 3) :
    IsStableUnder (gaugeLorentzMaps repGaugeGroupI repLorentzGroup)
      (LocalCovFieldAlgebra.leptonBlockSubmodule f f') :=
  IsStableUnder.mul (gaugeLorentzMaps_mul repGaugeGroupI_mul
    repLorentzGroup_mul)
    LocalCovFieldAlgebra.isStableUnder_higgsSubmodule_zero
    (IsStableUnder.mul (gaugeLorentzMaps_mul repGaugeGroupI_mul
      repLorentzGroup_mul)
      (LocalCovFieldAlgebra.isStableUnder_range_barL f) (LocalCovFieldAlgebra.isStableUnder_range_e
        f'))

/-- The conjugate down-type block submodule is carried into itself by both groups. -/
lemma isStableUnder_barDownBlockSubmodule (f f' : Fin 3) :
    IsStableUnder (gaugeLorentzMaps repGaugeGroupI repLorentzGroup)
      (LocalCovFieldAlgebra.barDownBlockSubmodule f f') :=
  IsStableUnder.mul (gaugeLorentzMaps_mul repGaugeGroupI_mul
    repLorentzGroup_mul)
    LocalCovFieldAlgebra.isStableUnder_barHiggsSubmodule_zero
    (IsStableUnder.mul (gaugeLorentzMaps_mul repGaugeGroupI_mul
      repLorentzGroup_mul)
      (LocalCovFieldAlgebra.isStableUnder_range_bard f) (LocalCovFieldAlgebra.isStableUnder_range_Q
        f'))

/-- The conjugate up-type block submodule is carried into itself by both groups. -/
lemma isStableUnder_barUpBlockSubmodule (f f' : Fin 3) :
    IsStableUnder (gaugeLorentzMaps repGaugeGroupI repLorentzGroup)
      (LocalCovFieldAlgebra.barUpBlockSubmodule f f') :=
  IsStableUnder.mul (gaugeLorentzMaps_mul repGaugeGroupI_mul
    repLorentzGroup_mul)
    LocalCovFieldAlgebra.isStableUnder_barHiggsSubmodule_zero
    (IsStableUnder.mul (gaugeLorentzMaps_mul repGaugeGroupI_mul
      repLorentzGroup_mul)
      (LocalCovFieldAlgebra.isStableUnder_range_u f) (LocalCovFieldAlgebra.isStableUnder_range_barQ
        f'))

/-- The conjugate charged-lepton block submodule is carried into itself by both groups. -/
lemma isStableUnder_barLeptonBlockSubmodule (f f' : Fin 3) :
    IsStableUnder (gaugeLorentzMaps repGaugeGroupI repLorentzGroup)
      (LocalCovFieldAlgebra.barLeptonBlockSubmodule f f') :=
  IsStableUnder.mul (gaugeLorentzMaps_mul repGaugeGroupI_mul
    repLorentzGroup_mul)
    LocalCovFieldAlgebra.isStableUnder_barHiggsSubmodule_zero
    (IsStableUnder.mul (gaugeLorentzMaps_mul repGaugeGroupI_mul
      repLorentzGroup_mul)
      (LocalCovFieldAlgebra.isStableUnder_range_L f) (LocalCovFieldAlgebra.isStableUnder_range_bare
        f'))

/-- The join of the six block submodules over the nine family pairs, the submodule the weight-zero
  piece of the Yukawa sector at mass weight eight is contained in. -/
noncomputable def blockSubmodule : Submodule ℂ fieldData.LocalCovFieldAlgebra :=
  ⨆ (f : Fin 3) (f' : Fin 3), LocalCovFieldAlgebra.downBlockSubmodule f f' ⊔
    LocalCovFieldAlgebra.upBlockSubmodule f f'
    ⊔ LocalCovFieldAlgebra.leptonBlockSubmodule f f' ⊔ LocalCovFieldAlgebra.barDownBlockSubmodule f
      f'
    ⊔ LocalCovFieldAlgebra.barUpBlockSubmodule f f' ⊔ LocalCovFieldAlgebra.barLeptonBlockSubmodule f
      f'

/-- A Yukawa product with its two fermion factors in the transposed order lies in any
  submodule containing the product in the original order, the two fermion ranges commuting. -/
lemma mul_mul_le_of_swap {H A B W : Submodule ℂ fieldData.LocalCovFieldAlgebra}
    (hA : A ≤ FermionSector.derivSubmodule 0) (hB : B ≤ FermionSector.derivSubmodule 0)
    (h : H * (B * A) ≤ W) : H * (A * B) ≤ W := by
  rwa [mul_comm_of_le_derivSubmodule hA hB]

/-- The weight-zero piece of the Yukawa sector at mass weight eight lies in the join of the
  six block submodules over the nine family pairs. The twelve blocks of
  `sectorMassWeightEightGaugeWeight_piece_zero` become six because the two fermion factors
  of a block commute, so the transposed block of `(f, f')` is the block of `(f', f)`; and
  the weight refinement inside a block is dropped, hypercharge having already done its
  work and colour, isospin and Lorentz being what decide the rest. -/
lemma sectorMassWeightEightGaugeWeight_piece_zero_le :
    LocalCovFieldAlgebra.sectorMassWeightEightGaugeWeight.piece 0 ≤
      LocalCovFieldAlgebra.blockSubmodule := by
  rw [LocalCovFieldAlgebra.sectorMassWeightEightGaugeWeight_piece_zero, blockSubmodule]
  refine iSup_le fun f => iSup_le fun f' => ?_
  refine sup_le (sup_le (sup_le (sup_le (sup_le (sup_le (sup_le (sup_le (sup_le
    (sup_le (sup_le ?_ ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_
  · exact le_trans (GaugeWeightDecomposition.piece_le_self _ 0)
      (le_iSup₂_of_le f f' (le_sup_of_le_left (le_sup_of_le_left
        (le_sup_of_le_left (le_sup_of_le_left le_sup_left)))))
  · exact (GaugeWeightDecomposition.piece_le_self _ 0).trans (mul_mul_le_of_swap
      (range_barQ_le_derivSubmodule f ![]) (range_d_le_derivSubmodule f' ![])
      (le_iSup₂_of_le f' f (le_sup_of_le_left (le_sup_of_le_left
      (le_sup_of_le_left (le_sup_of_le_left le_sup_left))))))
  · exact le_trans (GaugeWeightDecomposition.piece_le_self _ 0)
      (le_iSup₂_of_le f f' (le_sup_of_le_left (le_sup_of_le_left
        (le_sup_of_le_left (le_sup_of_le_left le_sup_right)))))
  · exact (GaugeWeightDecomposition.piece_le_self _ 0).trans (mul_mul_le_of_swap
      (range_Q_le_derivSubmodule f ![]) (range_baru_le_derivSubmodule f' ![])
      (le_iSup₂_of_le f' f (le_sup_of_le_left (le_sup_of_le_left
      (le_sup_of_le_left (le_sup_of_le_left le_sup_right))))))
  · exact le_trans (GaugeWeightDecomposition.piece_le_self _ 0)
      (le_iSup₂_of_le f f' (le_sup_of_le_left (le_sup_of_le_left
        (le_sup_of_le_left le_sup_right))))
  · exact (GaugeWeightDecomposition.piece_le_self _ 0).trans (mul_mul_le_of_swap
      (range_e_le_derivSubmodule f ![]) (range_barL_le_derivSubmodule f' ![])
      (le_iSup₂_of_le f' f (le_sup_of_le_left (le_sup_of_le_left
      (le_sup_of_le_left le_sup_right)))))
  · exact le_trans (GaugeWeightDecomposition.piece_le_self _ 0)
      (le_iSup₂_of_le f f' (le_sup_of_le_left (le_sup_of_le_left le_sup_right)))
  · exact (GaugeWeightDecomposition.piece_le_self _ 0).trans (mul_mul_le_of_swap
      (range_Q_le_derivSubmodule f ![]) (range_bard_le_derivSubmodule f' ![])
      (le_iSup₂_of_le f' f (le_sup_of_le_left (le_sup_of_le_left le_sup_right))))
  · exact le_trans (GaugeWeightDecomposition.piece_le_self _ 0)
      (le_iSup₂_of_le f f' (le_sup_of_le_left le_sup_right))
  · exact (GaugeWeightDecomposition.piece_le_self _ 0).trans (mul_mul_le_of_swap
      (range_barQ_le_derivSubmodule f ![]) (range_u_le_derivSubmodule f' ![])
      (le_iSup₂_of_le f' f (le_sup_of_le_left le_sup_right)))
  · exact le_trans (GaugeWeightDecomposition.piece_le_self _ 0)
      (le_iSup₂_of_le f f' le_sup_right)
  · exact (GaugeWeightDecomposition.piece_le_self _ 0).trans (mul_mul_le_of_swap
      (range_bare_le_derivSubmodule f ![]) (range_L_le_derivSubmodule f' ![])
      (le_iSup₂_of_le f' f le_sup_right))

/-!

## D. The blocks reduce to the Yukawa terms

Each block is classified in three stages, and each stage is the same move: one index law
holds at every value of the indices it does not see, so a family of steps is applied at
once by `InvariantReductionToSpan.reducesInvariantsTo_iSup`, and what comes out is the span of
the contractions, which is the source of the next stage. Colour first, then isospin, then Lorentz —
the order is forced, each contraction being a spectator of the ones after it.

The two lepton blocks have no colour index at all, so their first stage is
`InvariantReductionToSpan.ofFixed` rather than a classification: the block is already fixed by the
colour factor and the stage reduces it to itself. That keeps them in the same three-stage shape as
the four quark blocks.

-/

/-- The down-type block reduces to the down-type Yukawa term. -/
lemma reducesInvariantsTo_downYukawa (f f' : Fin 3) :
    ReducesInvariantsTo (gaugeLorentzMaps repGaugeGroupI
      repLorentzGroup) (LocalCovFieldAlgebra.downBlockSubmodule f f')
      (ℂ ∙ LocalCovFieldAlgebra.downYukawa f f') := by
  have hcolour : ReducesInvariantsTo (gaugeLorentzMaps repGaugeGroupI
    repLorentzGroup)
      (LocalCovFieldAlgebra.downBlockSubmodule f f')
      (Submodule.span ℂ (Set.range fun k : Fin 2 × Fin 2 × Fin 2 × Fin 2 =>
        LocalCovFieldAlgebra.downBlockColour f f' k.1 k.2.1 k.2.2.1 k.2.2.2)) := by
    refine ReducesInvariantsTo.ofSU3 ((InvariantReductionToSpan.reducesInvariantsTo_iSup
      fun k : Fin 2 × Fin 2 × Fin 2 × Fin 2 =>
        ColourFundAntiFund.invariantReductionToSpan
          (LocalCovFieldAlgebra.isEquivariant_colourFundAntiFund_downBlock f f' k.1 k.2.1 k.2.2.1
            k.2.2.2)).mono_left ?_)
    rw [downBlockSubmodule]
    refine Submodule.mul_mul_le_of_le_span_range LocalCovFieldAlgebra.higgsSubmodule_zero_le
      (le_of_eq (LocalCovFieldAlgebra.range_d_eq f))
        (le_of_eq (LocalCovFieldAlgebra.range_barQ_eq f')) fun i j k => ?_
    rw [show ScalarSector.higgs ![] i * (FermionSector.dComponent f ![] j *
        FermionSector.barQComponent f' ![] k)
        = LocalCovFieldAlgebra.downBlock f f' i j.1 (![k.2.1, j.2] 1) k.1 (![k.2.1, j.2] 0) k.2.2
          from by
      simp [downBlock]]
    exact Submodule.mem_iSup_of_mem (i, j.1, k.1, k.2.2) (Submodule.subset_span ⟨_, rfl⟩)
  have hisospin : ReducesInvariantsTo (gaugeLorentzMaps repGaugeGroupI
    repLorentzGroup)
      (Submodule.span ℂ (Set.range fun k : Fin 2 × Fin 2 × Fin 2 × Fin 2 =>
        LocalCovFieldAlgebra.downBlockColour f f' k.1 k.2.1 k.2.2.1 k.2.2.2))
      (Submodule.span ℂ
        (Set.range fun m : Fin 2 × Fin 2 =>
          LocalCovFieldAlgebra.downBlockIsospin f f' m.1 m.2)) := by
    refine ReducesInvariantsTo.ofSU2 ((InvariantReductionToSpan.reducesInvariantsTo_iSup
      fun m : Fin 2 × Fin 2 =>
        IsospinFundAntiFund.invariantReductionToSpan
          (LocalCovFieldAlgebra.isEquivariant_isospinFundAntiFund_downBlockColour f f' m.1
            m.2)).mono_left ?_)
    refine Submodule.span_le.2 <| Set.range_subset_iff.2 fun k =>
      Submodule.mem_iSup_of_mem (k.2.1, k.2.2.1) ?_
    rw [show LocalCovFieldAlgebra.downBlockColour f f' k.1 k.2.1 k.2.2.1 k.2.2.2
        = LocalCovFieldAlgebra.downBlockColour f f' (![k.2.2.2, k.1] 1) k.2.1 k.2.2.1
          (![k.2.2.2, k.1] 0)
        from by simp]
    exact Submodule.subset_span ⟨_, rfl⟩
  exact (hcolour.trans hisospin).trans (ReducesInvariantsTo.ofLorentz
    ((invariantReductionToMetricTensor
      (LocalCovFieldAlgebra.isEquivariant_downRDownR_downBlockIsospin f
          f')).reducesInvariantsTo.mono_left
        (range_liftComponents_pair (S := complexLorentzTensor) (c1 := .downR) (c2 := .downR)
            (LocalCovFieldAlgebra.downBlockIsospin
          f f')).ge))

/-- The up-type block reduces to the up-type Yukawa term. Isospin is contracted by the
  antisymmetric symbol here, the Higgs symbol and the quark doublet both carrying the
  anti-fundamental. -/
lemma reducesInvariantsTo_upYukawa (f f' : Fin 3) :
    ReducesInvariantsTo (gaugeLorentzMaps repGaugeGroupI
      repLorentzGroup) (LocalCovFieldAlgebra.upBlockSubmodule f f')
      (ℂ ∙ LocalCovFieldAlgebra.upYukawa f f') := by
  have hcolour : ReducesInvariantsTo (gaugeLorentzMaps repGaugeGroupI
    repLorentzGroup)
      (LocalCovFieldAlgebra.upBlockSubmodule f f')
      (Submodule.span ℂ (Set.range fun k : Fin 2 × Fin 2 × Fin 2 × Fin 2 =>
        LocalCovFieldAlgebra.upBlockColour f f' k.1 k.2.1 k.2.2.1 k.2.2.2)) := by
    refine ReducesInvariantsTo.ofSU3 ((InvariantReductionToSpan.reducesInvariantsTo_iSup
      fun k : Fin 2 × Fin 2 × Fin 2 × Fin 2 =>
        ColourFundAntiFund.invariantReductionToSpan
          (LocalCovFieldAlgebra.isEquivariant_colourFundAntiFund_upBlock f f' k.1 k.2.1 k.2.2.1
            k.2.2.2)).mono_left ?_)
    rw [upBlockSubmodule]
    refine Submodule.mul_mul_le_of_le_span_range LocalCovFieldAlgebra.higgsSubmodule_zero_le
      (le_of_eq (LocalCovFieldAlgebra.range_baru_eq f))
        (le_of_eq (LocalCovFieldAlgebra.range_Q_eq f')) fun i j k => ?_
    rw [show ScalarSector.higgs ![] i * (FermionSector.baruComponent f ![] j *
        FermionSector.QComponent f' ![] k)
        = LocalCovFieldAlgebra.upBlock f f' i j.1 (![j.2, k.2.1] 0) k.1 (![j.2, k.2.1] 1)
          k.2.2 from by
      simp [upBlock]]
    exact Submodule.mem_iSup_of_mem (i, j.1, k.1, k.2.2) (Submodule.subset_span ⟨_, rfl⟩)
  have hisospin : ReducesInvariantsTo (gaugeLorentzMaps repGaugeGroupI
    repLorentzGroup)
      (Submodule.span ℂ (Set.range fun k : Fin 2 × Fin 2 × Fin 2 × Fin 2 =>
        LocalCovFieldAlgebra.upBlockColour f f' k.1 k.2.1 k.2.2.1 k.2.2.2))
      (Submodule.span ℂ
        (Set.range fun m : Fin 2 × Fin 2 => LocalCovFieldAlgebra.upBlockIsospin f f' m.1 m.2)) := by
    refine ReducesInvariantsTo.ofSU2 ((InvariantReductionToSpan.reducesInvariantsTo_iSup
      fun m : Fin 2 × Fin 2 =>
        IsospinAntiFundAntiFund.invariantReductionToSpan
          (LocalCovFieldAlgebra.isEquivariant_isospinAntiFundAntiFund_upBlockColour f f' m.1
              m.2)).mono_left ?_)
    refine Submodule.span_le.2 <| Set.range_subset_iff.2 fun k =>
      Submodule.mem_iSup_of_mem (k.2.1, k.2.2.1) ?_
    rw [show LocalCovFieldAlgebra.upBlockColour f f' k.1 k.2.1 k.2.2.1 k.2.2.2
        = LocalCovFieldAlgebra.upBlockColour f f' (![k.1, k.2.2.2] 0) k.2.1 k.2.2.1
          (![k.1, k.2.2.2] 1)
        from by simp]
    exact Submodule.subset_span ⟨_, rfl⟩
  exact (hcolour.trans hisospin).trans (ReducesInvariantsTo.ofLorentz
    ((invariantReductionToMetricTensor
      (LocalCovFieldAlgebra.isEquivariant_downLDownL_upBlockIsospin f
          f')).reducesInvariantsTo.mono_left
        (range_liftComponents_pair (S := complexLorentzTensor) (c1 := .downL) (c2 := .downL)
            (LocalCovFieldAlgebra.upBlockIsospin f
          f')).ge))

/-- The charged-lepton block reduces to the charged-lepton Yukawa term. Its colour stage is
  the trivial one. The three symbols carry no colour index between them, so the block is
  fixed by the colour factor and the stage reduces it to itself. -/
lemma reducesInvariantsTo_leptonYukawa (f f' : Fin 3) :
    ReducesInvariantsTo (gaugeLorentzMaps repGaugeGroupI
      repLorentzGroup) (LocalCovFieldAlgebra.leptonBlockSubmodule f f')
      (ℂ ∙ LocalCovFieldAlgebra.leptonYukawa f f') := by
  have hcolour : ReducesInvariantsTo (gaugeLorentzMaps repGaugeGroupI
    repLorentzGroup)
      (LocalCovFieldAlgebra.leptonBlockSubmodule f f')
      (Submodule.span ℂ (Set.range fun k : Fin 2 × Fin 2 × Fin 2 × Fin 2 =>
        LocalCovFieldAlgebra.leptonBlock f f' k.1 k.2.1 k.2.2.1 k.2.2.2)) := by
    refine ReducesInvariantsTo.ofSU3 ((InvariantReductionToSpan.reducesInvariantsTo_iSup
      fun k : Fin 2 × Fin 2 × Fin 2 × Fin 2 =>
        InvariantReductionToSpan.ofFixed (LocalCovFieldAlgebra.leptonBlock f f' k.1 k.2.1 k.2.2.1
          k.2.2.2)
          fun U => LocalCovFieldAlgebra.repGauge_su3_leptonBlock U f f' k.1 k.2.1 k.2.2.1
            k.2.2.2).mono_left ?_)
    rw [leptonBlockSubmodule]
    refine Submodule.mul_mul_le_of_le_span_range LocalCovFieldAlgebra.higgsSubmodule_zero_le
      (le_of_eq (LocalCovFieldAlgebra.range_barL_eq f))
        (le_of_eq (LocalCovFieldAlgebra.range_e_eq f')) fun i j k => ?_
    rw [show ScalarSector.higgs ![] i * (FermionSector.barLComponent f ![] j *
        FermionSector.eComponent f' ![] k)
        = LocalCovFieldAlgebra.leptonBlock f f' i j.1 j.2 k from by simp [leptonBlock]]
    exact Submodule.mem_iSup_of_mem (i, j.1, j.2, k) (Submodule.mem_span_singleton_self _)
  have hisospin : ReducesInvariantsTo (gaugeLorentzMaps repGaugeGroupI
    repLorentzGroup)
      (Submodule.span ℂ (Set.range fun k : Fin 2 × Fin 2 × Fin 2 × Fin 2 =>
        LocalCovFieldAlgebra.leptonBlock f f' k.1 k.2.1 k.2.2.1 k.2.2.2))
      (Submodule.span ℂ
        (Set.range fun m : Fin 2 × Fin 2 => LocalCovFieldAlgebra.leptonBlockIsospin f f' m.1
          m.2)) := by
    refine ReducesInvariantsTo.ofSU2 ((InvariantReductionToSpan.reducesInvariantsTo_iSup
      fun m : Fin 2 × Fin 2 =>
        IsospinFundAntiFund.invariantReductionToSpan
          (LocalCovFieldAlgebra.isEquivariant_isospinFundAntiFund_leptonBlock f f' m.1
              m.2)).mono_left
            ?_)
    refine Submodule.span_le.2 <| Set.range_subset_iff.2 fun k =>
      Submodule.mem_iSup_of_mem (k.2.1, k.2.2.2) ?_
    rw [show LocalCovFieldAlgebra.leptonBlock f f' k.1 k.2.1 k.2.2.1 k.2.2.2
        = LocalCovFieldAlgebra.leptonBlock f f' (![k.2.2.1, k.1] 1) k.2.1 (![k.2.2.1, k.1] 0)
          k.2.2.2
        from by simp]
    exact Submodule.subset_span ⟨_, rfl⟩
  exact (hcolour.trans hisospin).trans (ReducesInvariantsTo.ofLorentz
    ((invariantReductionToMetricTensor
      (LocalCovFieldAlgebra.isEquivariant_downRDownR_leptonBlockIsospin f
        f')).reducesInvariantsTo.mono_left
        (range_liftComponents_pair (S := complexLorentzTensor) (c1 := .downR) (c2 := .downR)
          (LocalCovFieldAlgebra.leptonBlockIsospin f f')).ge))

/-- The conjugate down-type block reduces to the conjugate down-type Yukawa term. -/
lemma reducesInvariantsTo_barDownYukawa (f f' : Fin 3) :
    ReducesInvariantsTo (gaugeLorentzMaps repGaugeGroupI
      repLorentzGroup) (LocalCovFieldAlgebra.barDownBlockSubmodule f f')
      (ℂ ∙ LocalCovFieldAlgebra.barDownYukawa f f') := by
  have hcolour : ReducesInvariantsTo (gaugeLorentzMaps repGaugeGroupI
    repLorentzGroup)
      (LocalCovFieldAlgebra.barDownBlockSubmodule f f')
      (Submodule.span ℂ (Set.range fun k : Fin 2 × Fin 2 × Fin 2 × Fin 2 =>
        LocalCovFieldAlgebra.barDownBlockColour f f' k.1 k.2.1 k.2.2.1 k.2.2.2)) := by
    refine ReducesInvariantsTo.ofSU3 ((InvariantReductionToSpan.reducesInvariantsTo_iSup
      fun k : Fin 2 × Fin 2 × Fin 2 × Fin 2 =>
        ColourFundAntiFund.invariantReductionToSpan
          (LocalCovFieldAlgebra.isEquivariant_colourFundAntiFund_barDownBlock f f' k.1 k.2.1 k.2.2.1
            k.2.2.2)).mono_left ?_)
    rw [barDownBlockSubmodule]
    refine Submodule.mul_mul_le_of_le_span_range LocalCovFieldAlgebra.barHiggsSubmodule_zero_le
      (le_of_eq (LocalCovFieldAlgebra.range_bard_eq f))
        (le_of_eq (LocalCovFieldAlgebra.range_Q_eq f')) fun i j k => ?_
    rw [show ScalarSector.barHiggs ![] i * (FermionSector.bardComponent f ![] j *
        FermionSector.QComponent f' ![] k)
        = LocalCovFieldAlgebra.barDownBlock f f' i j.1 (![j.2, k.2.1] 0) k.1 (![j.2, k.2.1] 1) k.2.2
          from by
      simp [barDownBlock]]
    exact Submodule.mem_iSup_of_mem (i, j.1, k.1, k.2.2) (Submodule.subset_span ⟨_, rfl⟩)
  have hisospin : ReducesInvariantsTo (gaugeLorentzMaps repGaugeGroupI
    repLorentzGroup)
      (Submodule.span ℂ (Set.range fun k : Fin 2 × Fin 2 × Fin 2 × Fin 2 =>
        LocalCovFieldAlgebra.barDownBlockColour f f' k.1 k.2.1 k.2.2.1 k.2.2.2))
      (Submodule.span ℂ
        (Set.range fun m : Fin 2 × Fin 2 => LocalCovFieldAlgebra.barDownBlockIsospin f f' m.1
          m.2)) := by
    refine ReducesInvariantsTo.ofSU2 ((InvariantReductionToSpan.reducesInvariantsTo_iSup
      fun m : Fin 2 × Fin 2 =>
        IsospinFundAntiFund.invariantReductionToSpan
          (LocalCovFieldAlgebra.isEquivariant_isospinFundAntiFund_barDownBlockColour f f' m.1
            m.2)).mono_left ?_)
    refine Submodule.span_le.2 <| Set.range_subset_iff.2 fun k =>
      Submodule.mem_iSup_of_mem (k.2.1, k.2.2.1) ?_
    rw [show LocalCovFieldAlgebra.barDownBlockColour f f' k.1 k.2.1 k.2.2.1 k.2.2.2
        = LocalCovFieldAlgebra.barDownBlockColour f f' (![k.1, k.2.2.2] 0) k.2.1 k.2.2.1
          (![k.1, k.2.2.2] 1)
        from by simp]
    exact Submodule.subset_span ⟨_, rfl⟩
  exact (hcolour.trans hisospin).trans (ReducesInvariantsTo.ofLorentz
    ((invariantReductionToMetricTensor
      (LocalCovFieldAlgebra.isEquivariant_downLDownL_barDownBlockIsospin f
        f')).reducesInvariantsTo.mono_left
        (range_liftComponents_pair (S := complexLorentzTensor) (c1 := .downL) (c2 := .downL)
          (LocalCovFieldAlgebra.barDownBlockIsospin f f')).ge))

/-- The conjugate up-type block reduces to the conjugate up-type Yukawa term. -/
lemma reducesInvariantsTo_barUpYukawa (f f' : Fin 3) :
    ReducesInvariantsTo (gaugeLorentzMaps repGaugeGroupI
      repLorentzGroup) (LocalCovFieldAlgebra.barUpBlockSubmodule f f')
      (ℂ ∙ LocalCovFieldAlgebra.barUpYukawa f f') := by
  have hcolour : ReducesInvariantsTo (gaugeLorentzMaps repGaugeGroupI
    repLorentzGroup)
      (LocalCovFieldAlgebra.barUpBlockSubmodule f f')
      (Submodule.span ℂ (Set.range fun k : Fin 2 × Fin 2 × Fin 2 × Fin 2 =>
        LocalCovFieldAlgebra.barUpBlockColour f f' k.1 k.2.1 k.2.2.1 k.2.2.2)) := by
    refine ReducesInvariantsTo.ofSU3 ((InvariantReductionToSpan.reducesInvariantsTo_iSup
      fun k : Fin 2 × Fin 2 × Fin 2 × Fin 2 =>
        ColourFundAntiFund.invariantReductionToSpan
          (LocalCovFieldAlgebra.isEquivariant_colourFundAntiFund_barUpBlock f f' k.1 k.2.1 k.2.2.1
            k.2.2.2)).mono_left ?_)
    rw [barUpBlockSubmodule]
    refine Submodule.mul_mul_le_of_le_span_range LocalCovFieldAlgebra.barHiggsSubmodule_zero_le
      (le_of_eq (LocalCovFieldAlgebra.range_u_eq f))
        (le_of_eq (LocalCovFieldAlgebra.range_barQ_eq f')) fun i j k => ?_
    rw [show ScalarSector.barHiggs ![] i * (FermionSector.uComponent f ![] j *
        FermionSector.barQComponent f' ![] k)
        = LocalCovFieldAlgebra.barUpBlock f f' i j.1 (![k.2.1, j.2] 1) k.1 (![k.2.1, j.2] 0) k.2.2
          from by
      simp [barUpBlock]]
    exact Submodule.mem_iSup_of_mem (i, j.1, k.1, k.2.2) (Submodule.subset_span ⟨_, rfl⟩)
  have hisospin : ReducesInvariantsTo (gaugeLorentzMaps repGaugeGroupI
    repLorentzGroup)
      (Submodule.span ℂ (Set.range fun k : Fin 2 × Fin 2 × Fin 2 × Fin 2 =>
        LocalCovFieldAlgebra.barUpBlockColour f f' k.1 k.2.1 k.2.2.1 k.2.2.2))
      (Submodule.span ℂ
        (Set.range fun m : Fin 2 × Fin 2 =>
          LocalCovFieldAlgebra.barUpBlockIsospin f f' m.1 m.2)) := by
    refine ReducesInvariantsTo.ofSU2 ((InvariantReductionToSpan.reducesInvariantsTo_iSup
      fun m : Fin 2 × Fin 2 =>
        IsospinFundFund.invariantReductionToSpan
          (LocalCovFieldAlgebra.isEquivariant_isospinFundFund_barUpBlockColour f f' m.1
              m.2)).mono_left ?_)
    refine Submodule.span_le.2 <| Set.range_subset_iff.2 fun k =>
      Submodule.mem_iSup_of_mem (k.2.1, k.2.2.1) ?_
    rw [show LocalCovFieldAlgebra.barUpBlockColour f f' k.1 k.2.1 k.2.2.1 k.2.2.2
        = LocalCovFieldAlgebra.barUpBlockColour f f' (![k.1, k.2.2.2] 0) k.2.1 k.2.2.1
          (![k.1, k.2.2.2] 1)
        from by simp]
    exact Submodule.subset_span ⟨_, rfl⟩
  exact (hcolour.trans hisospin).trans (ReducesInvariantsTo.ofLorentz
    ((invariantReductionToMetricTensor
      (LocalCovFieldAlgebra.isEquivariant_downRDownR_barUpBlockIsospin f
          f')).reducesInvariantsTo.mono_left
        (range_liftComponents_pair (S := complexLorentzTensor) (c1 := .downR) (c2 := .downR)
            (LocalCovFieldAlgebra.barUpBlockIsospin
          f f')).ge))

/-- The conjugate charged-lepton block reduces to the conjugate charged-lepton Yukawa term,
  again with the trivial colour stage. -/
lemma reducesInvariantsTo_barLeptonYukawa (f f' : Fin 3) :
    ReducesInvariantsTo (gaugeLorentzMaps repGaugeGroupI
      repLorentzGroup) (LocalCovFieldAlgebra.barLeptonBlockSubmodule f f')
      (ℂ ∙ LocalCovFieldAlgebra.barLeptonYukawa f f') := by
  have hcolour : ReducesInvariantsTo (gaugeLorentzMaps repGaugeGroupI
    repLorentzGroup)
      (LocalCovFieldAlgebra.barLeptonBlockSubmodule f f')
      (Submodule.span ℂ (Set.range fun k : Fin 2 × Fin 2 × Fin 2 × Fin 2 =>
        LocalCovFieldAlgebra.barLeptonBlock f f' k.1 k.2.1 k.2.2.1 k.2.2.2)) := by
    refine ReducesInvariantsTo.ofSU3 ((InvariantReductionToSpan.reducesInvariantsTo_iSup
      fun k : Fin 2 × Fin 2 × Fin 2 × Fin 2 =>
        InvariantReductionToSpan.ofFixed (LocalCovFieldAlgebra.barLeptonBlock f f' k.1 k.2.1 k.2.2.1
          k.2.2.2)
          fun U =>
            LocalCovFieldAlgebra.repGauge_su3_barLeptonBlock U f f' k.1 k.2.1 k.2.2.1
              k.2.2.2).mono_left ?_)
    rw [barLeptonBlockSubmodule]
    refine Submodule.mul_mul_le_of_le_span_range LocalCovFieldAlgebra.barHiggsSubmodule_zero_le
      (le_of_eq (LocalCovFieldAlgebra.range_L_eq f))
        (le_of_eq (LocalCovFieldAlgebra.range_bare_eq f')) fun i j k => ?_
    rw [show ScalarSector.barHiggs ![] i * (FermionSector.LComponent f ![] j *
        FermionSector.bareComponent f' ![] k)
        = LocalCovFieldAlgebra.barLeptonBlock f f' i j.1 j.2 k from by simp [barLeptonBlock]]
    exact Submodule.mem_iSup_of_mem (i, j.1, j.2, k) (Submodule.mem_span_singleton_self _)
  have hisospin : ReducesInvariantsTo (gaugeLorentzMaps repGaugeGroupI
    repLorentzGroup)
      (Submodule.span ℂ (Set.range fun k : Fin 2 × Fin 2 × Fin 2 × Fin 2 =>
        LocalCovFieldAlgebra.barLeptonBlock f f' k.1 k.2.1 k.2.2.1 k.2.2.2))
      (Submodule.span ℂ
        (Set.range fun m : Fin 2 × Fin 2 => LocalCovFieldAlgebra.barLeptonBlockIsospin f f' m.1
          m.2)) := by
    refine ReducesInvariantsTo.ofSU2 ((InvariantReductionToSpan.reducesInvariantsTo_iSup
      fun m : Fin 2 × Fin 2 =>
        IsospinFundAntiFund.invariantReductionToSpan
          (LocalCovFieldAlgebra.isEquivariant_isospinFundAntiFund_barLeptonBlock f f' m.1
            m.2)).mono_left ?_)
    refine Submodule.span_le.2 <| Set.range_subset_iff.2 fun k =>
      Submodule.mem_iSup_of_mem (k.2.1, k.2.2.2) ?_
    rw [show LocalCovFieldAlgebra.barLeptonBlock f f' k.1 k.2.1 k.2.2.1 k.2.2.2
        = LocalCovFieldAlgebra.barLeptonBlock f f' (![k.1, k.2.2.1] 0) k.2.1 (![k.1, k.2.2.1] 1)
          k.2.2.2
        from by simp]
    exact Submodule.subset_span ⟨_, rfl⟩
  exact (hcolour.trans hisospin).trans (ReducesInvariantsTo.ofLorentz
    ((invariantReductionToMetricTensor
      (LocalCovFieldAlgebra.isEquivariant_downLDownL_barLeptonBlockIsospin f
        f')).reducesInvariantsTo.mono_left
        (range_liftComponents_pair (S := complexLorentzTensor) (c1 := .downL) (c2 := .downL)
          (LocalCovFieldAlgebra.barLeptonBlockIsospin f f')).ge))

/-!

## E. The classification of the invariants of mass weight eight

The two directions meet.  Forwards: the torus reduces the sector to its weight-zero piece,
the piece lies in the six block submodules, and the blocks reduce to the Yukawa span.
Backwards: `yukawaSpan_le_inf` says the Yukawa span is made of invariants of the right mass
weight to begin with, which turns the reduction into an equivalence rather than a one-way
inclusion.

-/

/-- The Yukawa span is fixed pointwise by both groups, `yukawaSpan_le_inf` placing it inside
  both spaces of invariants. -/
lemma isFixedBy_yukawaSpan : IsFixedBy (gaugeLorentzMaps repGaugeGroupI
    repLorentzGroup) LocalCovFieldAlgebra.yukawaSpan := by
  intro p y hy
  obtain ⟨hmem, hL⟩ := Submodule.mem_inf.1 (LocalCovFieldAlgebra.yukawaSpan_le_inf hy)
  obtain ⟨-, hG⟩ := Submodule.mem_inf.1 hmem
  cases p with
  | inl g => exact (Representation.mem_invariants _ _).1 hG g
  | inr Λ => exact (Representation.mem_invariants _ _).1 hL Λ

/-- The line through a down-type Yukawa term lies in the Yukawa span. -/
lemma span_downYukawa_le_yukawaSpan (f f' : Fin 3) :
    ℂ ∙ LocalCovFieldAlgebra.downYukawa f f' ≤ LocalCovFieldAlgebra.yukawaSpan :=
  (Submodule.span_singleton_le_iff_mem _ _).2 (Submodule.mem_sup_left (Submodule.mem_sup_left
    (Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_left
      (Submodule.mem_iSup_of_mem f (Submodule.mem_iSup_of_mem f'
        (Submodule.mem_span_singleton_self _))))))))

/-- The line through an up-type Yukawa term lies in the Yukawa span. -/
lemma span_upYukawa_le_yukawaSpan (f f' : Fin 3) :
    ℂ ∙ LocalCovFieldAlgebra.upYukawa f f' ≤ LocalCovFieldAlgebra.yukawaSpan :=
  (Submodule.span_singleton_le_iff_mem _ _).2 (Submodule.mem_sup_left (Submodule.mem_sup_left
    (Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_right
      (Submodule.mem_iSup_of_mem f (Submodule.mem_iSup_of_mem f'
        (Submodule.mem_span_singleton_self _))))))))

/-- The line through a charged-lepton Yukawa term lies in the Yukawa span. -/
lemma span_leptonYukawa_le_yukawaSpan (f f' : Fin 3) :
    ℂ ∙ LocalCovFieldAlgebra.leptonYukawa f f' ≤ LocalCovFieldAlgebra.yukawaSpan :=
  (Submodule.span_singleton_le_iff_mem _ _).2 (Submodule.mem_sup_left (Submodule.mem_sup_left
    (Submodule.mem_sup_left (Submodule.mem_sup_right
      (Submodule.mem_iSup_of_mem f (Submodule.mem_iSup_of_mem f'
        (Submodule.mem_span_singleton_self _)))))))

/-- The line through a conjugate down-type Yukawa term lies in the Yukawa span. -/
lemma span_barDownYukawa_le_yukawaSpan (f f' : Fin 3) :
    ℂ ∙ LocalCovFieldAlgebra.barDownYukawa f f' ≤ LocalCovFieldAlgebra.yukawaSpan :=
  (Submodule.span_singleton_le_iff_mem _ _).2 (Submodule.mem_sup_left (Submodule.mem_sup_left
    (Submodule.mem_sup_right (Submodule.mem_iSup_of_mem f (Submodule.mem_iSup_of_mem f'
      (Submodule.mem_span_singleton_self _))))))

/-- The line through a conjugate up-type Yukawa term lies in the Yukawa span. -/
lemma span_barUpYukawa_le_yukawaSpan (f f' : Fin 3) :
    ℂ ∙ LocalCovFieldAlgebra.barUpYukawa f f' ≤ LocalCovFieldAlgebra.yukawaSpan :=
  (Submodule.span_singleton_le_iff_mem _ _).2 (Submodule.mem_sup_left
    (Submodule.mem_sup_right (Submodule.mem_iSup_of_mem f (Submodule.mem_iSup_of_mem f'
      (Submodule.mem_span_singleton_self _)))))

/-- The line through a conjugate charged-lepton Yukawa term lies in the Yukawa span. -/
lemma span_barLeptonYukawa_le_yukawaSpan (f f' : Fin 3) :
    ℂ ∙ LocalCovFieldAlgebra.barLeptonYukawa f f' ≤ LocalCovFieldAlgebra.yukawaSpan :=
  (Submodule.span_singleton_le_iff_mem _ _).2 (Submodule.mem_sup_right
    (Submodule.mem_iSup_of_mem f (Submodule.mem_iSup_of_mem f'
      (Submodule.mem_span_singleton_self _))))

/-- The join of the six block submodules over the nine family pairs reduces to the Yukawa
  span. The fifty-four blocks are taken one at a time, each in turn joining the error term
  of the others, which is what their stability is for. -/
lemma reducesInvariantsTo_yukawaSpan :
    ReducesInvariantsTo (gaugeLorentzMaps repGaugeGroupI
      repLorentzGroup) LocalCovFieldAlgebra.blockSubmodule
      LocalCovFieldAlgebra.yukawaSpan := by
  have hW : IsStableUnder (gaugeLorentzMaps repGaugeGroupI
    repLorentzGroup) LocalCovFieldAlgebra.yukawaSpan :=
    LocalCovFieldAlgebra.isFixedBy_yukawaSpan.isStableUnder
  have hblock : ∀ f f' : Fin 3, ReducesInvariantsTo (gaugeLorentzMaps repGaugeGroupI
    repLorentzGroup)
      (LocalCovFieldAlgebra.downBlockSubmodule f f' ⊔ LocalCovFieldAlgebra.upBlockSubmodule f f' ⊔
        LocalCovFieldAlgebra.leptonBlockSubmodule f f'
        ⊔ LocalCovFieldAlgebra.barDownBlockSubmodule f f' ⊔ LocalCovFieldAlgebra.barUpBlockSubmodule
          f f'
        ⊔ LocalCovFieldAlgebra.barLeptonBlockSubmodule f f') LocalCovFieldAlgebra.yukawaSpan := fun
          f f' =>
    ReducesInvariantsTo.sup (ReducesInvariantsTo.sup (ReducesInvariantsTo.sup
      (ReducesInvariantsTo.sup (ReducesInvariantsTo.sup
      ((LocalCovFieldAlgebra.reducesInvariantsTo_downYukawa f f').mono_right
        (LocalCovFieldAlgebra.span_downYukawa_le_yukawaSpan f f'))
      ((LocalCovFieldAlgebra.reducesInvariantsTo_upYukawa f f').mono_right
        (LocalCovFieldAlgebra.span_upYukawa_le_yukawaSpan f f'))
      (LocalCovFieldAlgebra.isStableUnder_upBlockSubmodule f f') hW)
      ((LocalCovFieldAlgebra.reducesInvariantsTo_leptonYukawa f f').mono_right
        (LocalCovFieldAlgebra.span_leptonYukawa_le_yukawaSpan f f'))
      (LocalCovFieldAlgebra.isStableUnder_leptonBlockSubmodule f f') hW)
      ((LocalCovFieldAlgebra.reducesInvariantsTo_barDownYukawa f f').mono_right
        (LocalCovFieldAlgebra.span_barDownYukawa_le_yukawaSpan f f'))
      (LocalCovFieldAlgebra.isStableUnder_barDownBlockSubmodule f f') hW)
      ((LocalCovFieldAlgebra.reducesInvariantsTo_barUpYukawa f f').mono_right
        (LocalCovFieldAlgebra.span_barUpYukawa_le_yukawaSpan f f'))
      (LocalCovFieldAlgebra.isStableUnder_barUpBlockSubmodule f f') hW)
      ((LocalCovFieldAlgebra.reducesInvariantsTo_barLeptonYukawa f f').mono_right
        (LocalCovFieldAlgebra.span_barLeptonYukawa_le_yukawaSpan f f'))
      (LocalCovFieldAlgebra.isStableUnder_barLeptonBlockSubmodule f f') hW
  have hstable : ∀ f f' : Fin 3, IsStableUnder (gaugeLorentzMaps repGaugeGroupI
    repLorentzGroup)
      (LocalCovFieldAlgebra.downBlockSubmodule f f' ⊔ LocalCovFieldAlgebra.upBlockSubmodule f f' ⊔
        LocalCovFieldAlgebra.leptonBlockSubmodule f f'
        ⊔ LocalCovFieldAlgebra.barDownBlockSubmodule f f' ⊔ LocalCovFieldAlgebra.barUpBlockSubmodule
          f f'
        ⊔ LocalCovFieldAlgebra.barLeptonBlockSubmodule f f') := fun f f' =>
    ((((LocalCovFieldAlgebra.isStableUnder_downBlockSubmodule f f').sup
      (LocalCovFieldAlgebra.isStableUnder_upBlockSubmodule f f')).sup
      (LocalCovFieldAlgebra.isStableUnder_leptonBlockSubmodule f f')).sup
      (LocalCovFieldAlgebra.isStableUnder_barDownBlockSubmodule f f')).sup
      (LocalCovFieldAlgebra.isStableUnder_barUpBlockSubmodule f f') |>.sup
      (LocalCovFieldAlgebra.isStableUnder_barLeptonBlockSubmodule f f')
  rw [blockSubmodule]
  exact ReducesInvariantsTo.iSup (fun f => ReducesInvariantsTo.iSup (hblock f) (hstable f) hW)
    (fun f => isStableUnder_iSup (hstable f)) hW

/-- The Yukawa sector at mass weight eight reduces, for the gauge and Lorentz groups
  together, to the Yukawa span. Hypercharge puts an invariant in the weight-zero piece, the
  piece lies in the six block submodules, and colour, isospin and Lorentz reduce each block
  to its Yukawa term. -/
lemma reducesInvariantsTo_sectorMassWeight_higgs_fermion_eight :
    ReducesInvariantsTo (gaugeLorentzMaps repGaugeGroupI
      repLorentzGroup)
      (fieldData.sectorMassWeight {FieldKind.scalar, FieldKind.fermion} 8)
        LocalCovFieldAlgebra.yukawaSpan :=
  (ReducesInvariantsTo.ofGauge
    (ReducesInvariantsTo.comp (σ := fun g : GaugeGroupI => repGaugeGroupI g)
    gaugeTorusGen
      LocalCovFieldAlgebra.sectorMassWeightEightGaugeWeight.reducesInvariantsTo_piece_zero)).trans
    (LocalCovFieldAlgebra.reducesInvariantsTo_yukawaSpan.mono_left
      LocalCovFieldAlgebra.sectorMassWeightEightGaugeWeight_piece_zero_le)

/-- The classification of the Yukawa sector at mass weight eight as an equivalence. An
  element of the sector joined with a submodule `S` stable under both groups is fixed by
  both groups exactly when it is a combination of the six Yukawa couplings over the nine
  family pairs up to a remainder in `S` fixed by both groups. -/
lemma mem_sectorMassWeight_higgs_fermion_eight_sup_and_gauge_lorentz_invariant_iff
    (S : Submodule ℂ fieldData.LocalCovFieldAlgebra)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, repGaugeGroupI g
      y ∈ S)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentzGroup g y ∈ S) (x : fieldData.LocalCovFieldAlgebra) :
    (x ∈ fieldData.sectorMassWeight {FieldKind.scalar, FieldKind.fermion} 8 ⊔ S
        ∧ (∀ g : GaugeGroupI, repGaugeGroupI g x = x)
        ∧ ∀ g : SL(2,ℂ), repLorentzGroup g x = x)
      ↔ ∃ y ∈ S, (∀ g : GaugeGroupI, repGaugeGroupI g y = y)
          ∧ (∀ g : SL(2,ℂ), repLorentzGroup g y = y)
          ∧ x - y ∈ LocalCovFieldAlgebra.yukawaSpan :=
  ReducesInvariantsTo.mem_sup_and_gauge_lorentz_invariant_iff
    LocalCovFieldAlgebra.reducesInvariantsTo_sectorMassWeight_higgs_fermion_eight
    (LocalCovFieldAlgebra.yukawaSpan_le_inf.trans (inf_le_left.trans inf_le_left))
      LocalCovFieldAlgebra.isFixedBy_yukawaSpan hS hSL x

end LocalCovFieldAlgebra

end StandardModel
