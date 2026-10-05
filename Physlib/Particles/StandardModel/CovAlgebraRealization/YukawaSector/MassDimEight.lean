/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.CovAlgebraRealization.YukawaSector.Families.BarHiggs
public import Physlib.Particles.StandardModel.CovAlgebraRealization.YukawaSector.GaugeWeightDecomposition
/-!
# The Yukawa sector at mass weight eight

## i. Overview

This is the theorem the Yukawa sector exists for.  At mass weight eight the sector is one
Higgs tower against two underived fermion towers, and the claim proved here is that its
gauge- and Lorentz-invariant content, modulo a submodule `S` stable under both groups, is
exactly the span of the six Yukawa couplings over the nine family pairs.  Nothing else
survives: no fourth coupling, no extra colour or isospin structure inside a surviving
block, no invariant carrying a free spinor index.

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
`ReducesInvariantsTo σ V W`: a `σ`-invariant of `V ⊔ S` lies in `W ⊔ S` whenever `S` is
`σ`-stable. That relation composes — it is transitive, antitone in its source, monotone in its
target, and closed under joins of stable sources — and each `GaugeGroup` or `LorentzGroup`
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

-/

@[expose] public section

namespace StandardModel

open TensorProduct Matrix MatrixGroups Lorentz Pointwise ComplexConjugate

namespace CovAlgebraRealization

variable {B : Type} [Ring B] [Algebra ℂ B]
  {repGauge : Representation ℂ GaugeGroupI B}
  {repLorentz : Representation ℂ SL(2,ℂ) B}
  {massWeightPoly : B →ₐ[ℂ] Polynomial B}
  (h : CovAlgebraRealization B repGauge repLorentz massWeightPoly)

/-!

## A. The symbol ranges as spans of components

-/

/-- The Higgs submodule without derivatives lies in the span of the Higgs components. -/
lemma higgsSubmodule_zero_le :
    h.isHiggsSector.higgsSubmodule 0
      ≤ Submodule.span ℂ (Set.range (h.isHiggsSector.higgs ![])) := by
  refine iSup_le fun l => ?_
  rw [show l = (![] : Fin 0 → Fin 1 ⊕ Fin 3) from Subsingleton.elim _ _,
    LinearMap.range_eq_span_range_basis HiggsVec.orthonormBasis.toBasis.dualBasis
      (h.isHiggsSector.covH 0 ![])]
  exact le_rfl

/-- The conjugate Higgs submodule without derivatives lies in the span of the conjugate
  Higgs components. -/
lemma barHiggsSubmodule_zero_le :
    h.isHiggsSector.barHiggsSubmodule 0
      ≤ Submodule.span ℂ (Set.range (h.isHiggsSector.barHiggs ![])) := by
  refine iSup_le fun l => ?_
  rw [show l = (![] : Fin 0 → Fin 1 ⊕ Fin 3) from Subsingleton.elim _ _,
    LinearMap.range_eq_span_range_basis (Basis.conj HiggsVec.orthonormBasis.toBasis).dualBasis
      (h.isHiggsSector.covBarH 0 ![])]
  exact le_rfl

/-- The range of the down-singlet symbol map is the span of its components. -/
lemma range_d_eq (f : Fin 3) :
    LinearMap.range (h.covD f (![] : Fin 0 → Fin 1 ⊕ Fin 3))
      = Submodule.span ℂ (Set.range (h.isFermionSector.dComponent f ![])) :=
  LinearMap.range_eq_span_range_basis DownSinglet.basis.dualBasis (h.covD f ![])

/-- The range of the conjugate down-singlet symbol map is the span of its components. -/
lemma range_bard_eq (f : Fin 3) :
    LinearMap.range (h.covBarD f (![] : Fin 0 → Fin 1 ⊕ Fin 3))
      = Submodule.span ℂ (Set.range (h.isFermionSector.bardComponent f ![])) :=
  LinearMap.range_eq_span_range_basis (Basis.conj DownSinglet.basis).dualBasis (h.covBarD f ![])

/-- The range of the up-singlet symbol map is the span of its components. -/
lemma range_u_eq (f : Fin 3) :
    LinearMap.range (h.covU f (![] : Fin 0 → Fin 1 ⊕ Fin 3))
      = Submodule.span ℂ (Set.range (h.isFermionSector.uComponent f ![])) :=
  LinearMap.range_eq_span_range_basis UpSinglet.basis.dualBasis (h.covU f ![])

/-- The range of the conjugate up-singlet symbol map is the span of its components. -/
lemma range_baru_eq (f : Fin 3) :
    LinearMap.range (h.covBarU f (![] : Fin 0 → Fin 1 ⊕ Fin 3))
      = Submodule.span ℂ (Set.range (h.isFermionSector.baruComponent f ![])) :=
  LinearMap.range_eq_span_range_basis (Basis.conj UpSinglet.basis).dualBasis (h.covBarU f ![])

/-- The range of the quark-doublet symbol map is the span of its components. -/
lemma range_Q_eq (f : Fin 3) :
    LinearMap.range (h.covQ f (![] : Fin 0 → Fin 1 ⊕ Fin 3))
      = Submodule.span ℂ (Set.range (h.isFermionSector.QComponent f ![])) :=
  LinearMap.range_eq_span_range_basis QuarkDoublet.basis.dualBasis (h.covQ f ![])

/-- The range of the conjugate quark-doublet symbol map is the span of its components. -/
lemma range_barQ_eq (f : Fin 3) :
    LinearMap.range (h.covBarQ f (![] : Fin 0 → Fin 1 ⊕ Fin 3))
      = Submodule.span ℂ (Set.range (h.isFermionSector.barQComponent f ![])) :=
  LinearMap.range_eq_span_range_basis (Basis.conj QuarkDoublet.basis).dualBasis (h.covBarQ f ![])

/-- The range of the lepton-doublet symbol map is the span of its components. -/
lemma range_L_eq (f : Fin 3) :
    LinearMap.range (h.covL f (![] : Fin 0 → Fin 1 ⊕ Fin 3))
      = Submodule.span ℂ (Set.range (h.isFermionSector.LComponent f ![])) :=
  LinearMap.range_eq_span_range_basis LeptonDoublet.basis.dualBasis (h.covL f ![])

/-- The range of the conjugate lepton-doublet symbol map is the span of its components. -/
lemma range_barL_eq (f : Fin 3) :
    LinearMap.range (h.covBarL f (![] : Fin 0 → Fin 1 ⊕ Fin 3))
      = Submodule.span ℂ (Set.range (h.isFermionSector.barLComponent f ![])) :=
  LinearMap.range_eq_span_range_basis (Basis.conj LeptonDoublet.basis).dualBasis (h.covBarL f ![])

/-- The range of the lepton-singlet symbol map is the span of its components. -/
lemma range_e_eq (f : Fin 3) :
    LinearMap.range (h.covE f (![] : Fin 0 → Fin 1 ⊕ Fin 3))
      = Submodule.span ℂ (Set.range (h.isFermionSector.eComponent f ![])) :=
  LinearMap.range_eq_span_range_basis LeptonSinglet.basis.dualBasis (h.covE f ![])

/-- The range of the conjugate lepton-singlet symbol map is the span of its components. -/
lemma range_bare_eq (f : Fin 3) :
    LinearMap.range (h.covBarE f (![] : Fin 0 → Fin 1 ⊕ Fin 3))
      = Submodule.span ℂ (Set.range (h.isFermionSector.bareComponent f ![])) :=
  LinearMap.range_eq_span_range_basis (Basis.conj LeptonSinglet.basis).dualBasis (h.covBarE f ![])

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
    IsStableUnder (gaugeLorentzMaps repGauge repLorentz)
      (h.isHiggsSector.higgsSubmodule 0) := by
  refine isStableUnder_iSup fun l => isStableUnder_gaugeLorentzMaps_iff.2 ⟨?_, fun Λ => ?_⟩
  · exact isStableUnder_range_repGauge fun g φ => h.isHiggsSector.H_equivariant g φ 0 l
  · rw [show l = (![] : Fin 0 → Fin 1 ⊕ Fin 3) from Subsingleton.elim _ _]
    exact isStableUnder_range_repLorentz h.isHiggsSector.repLorentz_H Λ

/-- The conjugate Higgs submodule without derivatives is carried into itself by both
  groups. -/
lemma isStableUnder_barHiggsSubmodule_zero :
    IsStableUnder (gaugeLorentzMaps repGauge repLorentz)
      (h.isHiggsSector.barHiggsSubmodule 0) := by
  refine isStableUnder_iSup fun l => isStableUnder_gaugeLorentzMaps_iff.2 ⟨?_, fun Λ => ?_⟩
  · exact isStableUnder_range_repGauge fun g φ => h.isHiggsSector.barH_equivariant g φ 0 l
  · rw [show l = (![] : Fin 0 → Fin 1 ⊕ Fin 3) from Subsingleton.elim _ _]
    exact isStableUnder_range_repLorentz h.isHiggsSector.repLorentz_barH Λ

include h in
/-- The range of the down-singlet symbol map is carried into itself by both groups. -/
lemma isStableUnder_range_d (f : Fin 3) :
    IsStableUnder (gaugeLorentzMaps repGauge repLorentz)
      (LinearMap.range (h.covD f (![] : Fin 0 → Fin 1 ⊕ Fin 3))) :=
  isStableUnder_gaugeLorentzMaps_iff.2
    ⟨isStableUnder_range_repGauge fun g φ => h.isFermionSector.repGauge_d g f ![] φ,
      fun Λ => isStableUnder_range_repLorentz (h.isFermionSector.repLorentz_d f) Λ⟩

include h in
/-- The range of the conjugate down-singlet symbol map is carried into itself by both
  groups. -/
lemma isStableUnder_range_bard (f : Fin 3) :
    IsStableUnder (gaugeLorentzMaps repGauge repLorentz)
      (LinearMap.range (h.covBarD f (![] : Fin 0 → Fin 1 ⊕ Fin 3))) :=
  isStableUnder_gaugeLorentzMaps_iff.2
    ⟨isStableUnder_range_repGauge fun g φ => h.isFermionSector.repGauge_bard g f ![] φ,
      fun Λ => isStableUnder_range_repLorentz (h.isFermionSector.repLorentz_bard f) Λ⟩

include h in
/-- The range of the up-singlet symbol map is carried into itself by both groups. -/
lemma isStableUnder_range_u (f : Fin 3) :
    IsStableUnder (gaugeLorentzMaps repGauge repLorentz)
      (LinearMap.range (h.covU f (![] : Fin 0 → Fin 1 ⊕ Fin 3))) :=
  isStableUnder_gaugeLorentzMaps_iff.2
    ⟨isStableUnder_range_repGauge fun g φ => h.isFermionSector.repGauge_u g f ![] φ,
      fun Λ => isStableUnder_range_repLorentz (h.isFermionSector.repLorentz_u f) Λ⟩

include h in
/-- The range of the conjugate up-singlet symbol map is carried into itself by both
  groups. -/
lemma isStableUnder_range_baru (f : Fin 3) :
    IsStableUnder (gaugeLorentzMaps repGauge repLorentz)
      (LinearMap.range (h.covBarU f (![] : Fin 0 → Fin 1 ⊕ Fin 3))) :=
  isStableUnder_gaugeLorentzMaps_iff.2
    ⟨isStableUnder_range_repGauge fun g φ => h.isFermionSector.repGauge_baru g f ![] φ,
      fun Λ => isStableUnder_range_repLorentz (h.isFermionSector.repLorentz_baru f) Λ⟩

include h in
/-- The range of the quark-doublet symbol map is carried into itself by both groups. -/
lemma isStableUnder_range_Q (f : Fin 3) :
    IsStableUnder (gaugeLorentzMaps repGauge repLorentz)
      (LinearMap.range (h.covQ f (![] : Fin 0 → Fin 1 ⊕ Fin 3))) :=
  isStableUnder_gaugeLorentzMaps_iff.2
    ⟨isStableUnder_range_repGauge fun g φ => h.isFermionSector.repGauge_Q g f ![] φ,
      fun Λ => isStableUnder_range_repLorentz (h.isFermionSector.repLorentz_Q f) Λ⟩

include h in
/-- The range of the conjugate quark-doublet symbol map is carried into itself by both
  groups. -/
lemma isStableUnder_range_barQ (f : Fin 3) :
    IsStableUnder (gaugeLorentzMaps repGauge repLorentz)
      (LinearMap.range (h.covBarQ f (![] : Fin 0 → Fin 1 ⊕ Fin 3))) :=
  isStableUnder_gaugeLorentzMaps_iff.2
    ⟨isStableUnder_range_repGauge fun g φ => h.isFermionSector.repGauge_barQ g f ![] φ,
      fun Λ => isStableUnder_range_repLorentz (h.isFermionSector.repLorentz_barQ f) Λ⟩

include h in
/-- The range of the lepton-doublet symbol map is carried into itself by both groups. -/
lemma isStableUnder_range_L (f : Fin 3) :
    IsStableUnder (gaugeLorentzMaps repGauge repLorentz)
      (LinearMap.range (h.covL f (![] : Fin 0 → Fin 1 ⊕ Fin 3))) :=
  isStableUnder_gaugeLorentzMaps_iff.2
    ⟨isStableUnder_range_repGauge fun g φ => h.isFermionSector.repGauge_L g f ![] φ,
      fun Λ => isStableUnder_range_repLorentz (h.isFermionSector.repLorentz_L f) Λ⟩

include h in
/-- The range of the conjugate lepton-doublet symbol map is carried into itself by both
  groups. -/
lemma isStableUnder_range_barL (f : Fin 3) :
    IsStableUnder (gaugeLorentzMaps repGauge repLorentz)
      (LinearMap.range (h.covBarL f (![] : Fin 0 → Fin 1 ⊕ Fin 3))) :=
  isStableUnder_gaugeLorentzMaps_iff.2
    ⟨isStableUnder_range_repGauge fun g φ => h.isFermionSector.repGauge_barL g f ![] φ,
      fun Λ => isStableUnder_range_repLorentz (h.isFermionSector.repLorentz_barL f) Λ⟩

include h in
/-- The range of the lepton-singlet symbol map is carried into itself by both groups. -/
lemma isStableUnder_range_e (f : Fin 3) :
    IsStableUnder (gaugeLorentzMaps repGauge repLorentz)
      (LinearMap.range (h.covE f (![] : Fin 0 → Fin 1 ⊕ Fin 3))) :=
  isStableUnder_gaugeLorentzMaps_iff.2
    ⟨isStableUnder_range_repGauge fun g φ => h.isFermionSector.repGauge_e g f ![] φ,
      fun Λ => isStableUnder_range_repLorentz (h.isFermionSector.repLorentz_e f) Λ⟩

include h in
/-- The range of the conjugate lepton-singlet symbol map is carried into itself by both
  groups. -/
lemma isStableUnder_range_bare (f : Fin 3) :
    IsStableUnder (gaugeLorentzMaps repGauge repLorentz)
      (LinearMap.range (h.covBarE f (![] : Fin 0 → Fin 1 ⊕ Fin 3))) :=
  isStableUnder_gaugeLorentzMaps_iff.2
    ⟨isStableUnder_range_repGauge fun g φ => h.isFermionSector.repGauge_bare g f ![] φ,
      fun Λ => isStableUnder_range_repLorentz (h.isFermionSector.repLorentz_bare f) Λ⟩

/-!

## C. The twelve surviving blocks as six submodules

The twelve blocks that hypercharge leaves come in six transposed pairs, and a pair is one
submodule: the two fermion factors commute as submodules, by `mul_comm_of_le_derivSubmodule`,
so exchanging them changes nothing.  Under the join over family pairs the transposed block
of `(f, f')` is the untransposed block of `(f', f)`, and the weight-zero piece of the sector
lands inside the join of the six.

-/

/-- The submodule of the down-type block `H d barQ` of a family pair. -/
noncomputable def downBlockSubmodule (f f' : Fin 3) : Submodule ℂ B :=
  h.isHiggsSector.higgsSubmodule 0 * (LinearMap.range (h.covD f (![] : Fin 0 → Fin 1 ⊕ Fin 3))
    * LinearMap.range (h.covBarQ f' (![] : Fin 0 → Fin 1 ⊕ Fin 3)))

/-- The submodule of the up-type block `H baru Q` of a family pair. -/
noncomputable def upBlockSubmodule (f f' : Fin 3) : Submodule ℂ B :=
  h.isHiggsSector.higgsSubmodule 0 * (LinearMap.range (h.covBarU f (![] : Fin 0 → Fin 1 ⊕ Fin 3))
    * LinearMap.range (h.covQ f' (![] : Fin 0 → Fin 1 ⊕ Fin 3)))

/-- The submodule of the charged-lepton block `H barL e` of a family pair. -/
noncomputable def leptonBlockSubmodule (f f' : Fin 3) : Submodule ℂ B :=
  h.isHiggsSector.higgsSubmodule 0 * (LinearMap.range (h.covBarL f (![] : Fin 0 → Fin 1 ⊕ Fin 3))
    * LinearMap.range (h.covE f' (![] : Fin 0 → Fin 1 ⊕ Fin 3)))

/-- The submodule of the conjugate down-type block `barH bard Q` of a family pair. -/
noncomputable def barDownBlockSubmodule (f f' : Fin 3) : Submodule ℂ B :=
  h.isHiggsSector.barHiggsSubmodule 0
    * (LinearMap.range (h.covBarD f (![] : Fin 0 → Fin 1 ⊕ Fin 3))
      * LinearMap.range (h.covQ f' (![] : Fin 0 → Fin 1 ⊕ Fin 3)))

/-- The submodule of the conjugate up-type block `barH u barQ` of a family pair. -/
noncomputable def barUpBlockSubmodule (f f' : Fin 3) : Submodule ℂ B :=
  h.isHiggsSector.barHiggsSubmodule 0
    * (LinearMap.range (h.covU f (![] : Fin 0 → Fin 1 ⊕ Fin 3))
      * LinearMap.range (h.covBarQ f' (![] : Fin 0 → Fin 1 ⊕ Fin 3)))

/-- The submodule of the conjugate charged-lepton block `barH L bare` of a family pair. -/
noncomputable def barLeptonBlockSubmodule (f f' : Fin 3) : Submodule ℂ B :=
  h.isHiggsSector.barHiggsSubmodule 0
    * (LinearMap.range (h.covL f (![] : Fin 0 → Fin 1 ⊕ Fin 3))
      * LinearMap.range (h.covBarE f' (![] : Fin 0 → Fin 1 ⊕ Fin 3)))

/-- The down-type block submodule is carried into itself by both groups. -/
lemma isStableUnder_downBlockSubmodule (f f' : Fin 3) :
    IsStableUnder (gaugeLorentzMaps repGauge repLorentz) (h.downBlockSubmodule f f') :=
  IsStableUnder.mul (gaugeLorentzMaps_mul h.repGauge_mul h.repLorentz_mul)
    h.isStableUnder_higgsSubmodule_zero
    (IsStableUnder.mul (gaugeLorentzMaps_mul h.repGauge_mul h.repLorentz_mul)
      (h.isStableUnder_range_d f) (h.isStableUnder_range_barQ f'))

/-- The up-type block submodule is carried into itself by both groups. -/
lemma isStableUnder_upBlockSubmodule (f f' : Fin 3) :
    IsStableUnder (gaugeLorentzMaps repGauge repLorentz) (h.upBlockSubmodule f f') :=
  IsStableUnder.mul (gaugeLorentzMaps_mul h.repGauge_mul h.repLorentz_mul)
    h.isStableUnder_higgsSubmodule_zero
    (IsStableUnder.mul (gaugeLorentzMaps_mul h.repGauge_mul h.repLorentz_mul)
      (h.isStableUnder_range_baru f) (h.isStableUnder_range_Q f'))

/-- The charged-lepton block submodule is carried into itself by both groups. -/
lemma isStableUnder_leptonBlockSubmodule (f f' : Fin 3) :
    IsStableUnder (gaugeLorentzMaps repGauge repLorentz) (h.leptonBlockSubmodule f f') :=
  IsStableUnder.mul (gaugeLorentzMaps_mul h.repGauge_mul h.repLorentz_mul)
    h.isStableUnder_higgsSubmodule_zero
    (IsStableUnder.mul (gaugeLorentzMaps_mul h.repGauge_mul h.repLorentz_mul)
      (h.isStableUnder_range_barL f) (h.isStableUnder_range_e f'))

/-- The conjugate down-type block submodule is carried into itself by both groups. -/
lemma isStableUnder_barDownBlockSubmodule (f f' : Fin 3) :
    IsStableUnder (gaugeLorentzMaps repGauge repLorentz) (h.barDownBlockSubmodule f f') :=
  IsStableUnder.mul (gaugeLorentzMaps_mul h.repGauge_mul h.repLorentz_mul)
    h.isStableUnder_barHiggsSubmodule_zero
    (IsStableUnder.mul (gaugeLorentzMaps_mul h.repGauge_mul h.repLorentz_mul)
      (h.isStableUnder_range_bard f) (h.isStableUnder_range_Q f'))

/-- The conjugate up-type block submodule is carried into itself by both groups. -/
lemma isStableUnder_barUpBlockSubmodule (f f' : Fin 3) :
    IsStableUnder (gaugeLorentzMaps repGauge repLorentz) (h.barUpBlockSubmodule f f') :=
  IsStableUnder.mul (gaugeLorentzMaps_mul h.repGauge_mul h.repLorentz_mul)
    h.isStableUnder_barHiggsSubmodule_zero
    (IsStableUnder.mul (gaugeLorentzMaps_mul h.repGauge_mul h.repLorentz_mul)
      (h.isStableUnder_range_u f) (h.isStableUnder_range_barQ f'))

/-- The conjugate charged-lepton block submodule is carried into itself by both groups. -/
lemma isStableUnder_barLeptonBlockSubmodule (f f' : Fin 3) :
    IsStableUnder (gaugeLorentzMaps repGauge repLorentz) (h.barLeptonBlockSubmodule f f') :=
  IsStableUnder.mul (gaugeLorentzMaps_mul h.repGauge_mul h.repLorentz_mul)
    h.isStableUnder_barHiggsSubmodule_zero
    (IsStableUnder.mul (gaugeLorentzMaps_mul h.repGauge_mul h.repLorentz_mul)
      (h.isStableUnder_range_L f) (h.isStableUnder_range_bare f'))

/-- The join of the six block submodules over the nine family pairs: what the weight-zero
  piece of the Yukawa sector at mass weight eight is contained in. -/
noncomputable def blockSubmodule : Submodule ℂ B :=
  ⨆ (f : Fin 3) (f' : Fin 3), h.downBlockSubmodule f f' ⊔ h.upBlockSubmodule f f'
    ⊔ h.leptonBlockSubmodule f f' ⊔ h.barDownBlockSubmodule f f'
    ⊔ h.barUpBlockSubmodule f f' ⊔ h.barLeptonBlockSubmodule f f'

/-- The weight-zero piece of the Yukawa sector at mass weight eight lies in the join of the
  six block submodules over the nine family pairs. The twelve blocks of
  `sectorMassWeightEightGaugeWeight_piece_zero` become six because the two fermion factors
  of a block commute, so the transposed block of `(f, f')` is the block of `(f', f)`; and
  the weight refinement inside a block is dropped, hypercharge having already done its
  work and colour, isospin and Lorentz being what decide the rest. -/
lemma sectorMassWeightEightGaugeWeight_piece_zero_le :
    h.sectorMassWeightEightGaugeWeight.piece 0 ≤ h.blockSubmodule := by
  rw [h.sectorMassWeightEightGaugeWeight_piece_zero, blockSubmodule]
  refine iSup_le fun f => iSup_le fun f' => ?_
  refine sup_le (sup_le (sup_le (sup_le (sup_le (sup_le (sup_le (sup_le (sup_le
    (sup_le (sup_le ?_ ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_
  · exact le_trans (GaugeWeightDecomposition.piece_le_self _ 0)
      (le_iSup₂_of_le f f' (le_sup_of_le_left (le_sup_of_le_left
        (le_sup_of_le_left (le_sup_of_le_left le_sup_left)))))
  · refine le_trans (GaugeWeightDecomposition.piece_le_self _ 0) ?_
    rw [h.mul_comm_of_le_derivSubmodule (h.range_barQ_le_derivSubmodule f ![])
      (h.range_d_le_derivSubmodule f' ![])]
    exact le_iSup₂_of_le f' f (le_sup_of_le_left (le_sup_of_le_left
      (le_sup_of_le_left (le_sup_of_le_left le_sup_left))))
  · exact le_trans (GaugeWeightDecomposition.piece_le_self _ 0)
      (le_iSup₂_of_le f f' (le_sup_of_le_left (le_sup_of_le_left
        (le_sup_of_le_left (le_sup_of_le_left le_sup_right)))))
  · refine le_trans (GaugeWeightDecomposition.piece_le_self _ 0) ?_
    rw [h.mul_comm_of_le_derivSubmodule (h.range_Q_le_derivSubmodule f ![])
      (h.range_baru_le_derivSubmodule f' ![])]
    exact le_iSup₂_of_le f' f (le_sup_of_le_left (le_sup_of_le_left
      (le_sup_of_le_left (le_sup_of_le_left le_sup_right))))
  · exact le_trans (GaugeWeightDecomposition.piece_le_self _ 0)
      (le_iSup₂_of_le f f' (le_sup_of_le_left (le_sup_of_le_left
        (le_sup_of_le_left le_sup_right))))
  · refine le_trans (GaugeWeightDecomposition.piece_le_self _ 0) ?_
    rw [h.mul_comm_of_le_derivSubmodule (h.range_e_le_derivSubmodule f ![])
      (h.range_barL_le_derivSubmodule f' ![])]
    exact le_iSup₂_of_le f' f (le_sup_of_le_left (le_sup_of_le_left
      (le_sup_of_le_left le_sup_right)))
  · exact le_trans (GaugeWeightDecomposition.piece_le_self _ 0)
      (le_iSup₂_of_le f f' (le_sup_of_le_left (le_sup_of_le_left le_sup_right)))
  · refine le_trans (GaugeWeightDecomposition.piece_le_self _ 0) ?_
    rw [h.mul_comm_of_le_derivSubmodule (h.range_Q_le_derivSubmodule f ![])
      (h.range_bard_le_derivSubmodule f' ![])]
    exact le_iSup₂_of_le f' f (le_sup_of_le_left (le_sup_of_le_left le_sup_right))
  · exact le_trans (GaugeWeightDecomposition.piece_le_self _ 0)
      (le_iSup₂_of_le f f' (le_sup_of_le_left le_sup_right))
  · refine le_trans (GaugeWeightDecomposition.piece_le_self _ 0) ?_
    rw [h.mul_comm_of_le_derivSubmodule (h.range_barQ_le_derivSubmodule f ![])
      (h.range_u_le_derivSubmodule f' ![])]
    exact le_iSup₂_of_le f' f (le_sup_of_le_left le_sup_right)
  · exact le_trans (GaugeWeightDecomposition.piece_le_self _ 0)
      (le_iSup₂_of_le f f' le_sup_right)
  · refine le_trans (GaugeWeightDecomposition.piece_le_self _ 0) ?_
    rw [h.mul_comm_of_le_derivSubmodule (h.range_bare_le_derivSubmodule f ![])
      (h.range_L_le_derivSubmodule f' ![])]
    exact le_iSup₂_of_le f' f le_sup_right

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

include h in
/-- The down-type block reduces to the down-type Yukawa term. -/
lemma reducesInvariantsTo_downYukawa (f f' : Fin 3) :
    ReducesInvariantsTo (gaugeLorentzMaps repGauge repLorentz) (h.downBlockSubmodule f f')
      (ℂ ∙ h.downYukawa f f') := by
  have hcolour : ReducesInvariantsTo (gaugeLorentzMaps repGauge repLorentz)
      (h.downBlockSubmodule f f')
      (Submodule.span ℂ (Set.range fun k : Fin 2 × Fin 2 × Fin 2 × Fin 2 =>
        h.downBlockColour f f' k.1 k.2.1 k.2.2.1 k.2.2.2)) := by
    refine ReducesInvariantsTo.ofSU3 ((InvariantReductionToSpan.reducesInvariantsTo_iSup
      fun k : Fin 2 × Fin 2 × Fin 2 × Fin 2 =>
        IsSU3FundamentalAntiFundamental.invariantReductionToSpan
          (h.isSU3FundamentalAntiFundamental_downBlock f f' k.1 k.2.1 k.2.2.1
            k.2.2.2)).mono_left ?_)
    rw [downBlockSubmodule]
    refine Submodule.mul_mul_le_of_le_span_range h.higgsSubmodule_zero_le
      (le_of_eq (h.range_d_eq f)) (le_of_eq (h.range_barQ_eq f')) fun i j k => ?_
    rw [show h.isHiggsSector.higgs ![] i * (h.isFermionSector.dComponent f ![] j *
        h.isFermionSector.barQComponent f' ![] k)
        = h.downBlock f f' i j.1 (![k.2.1, j.2] 1) k.1 (![k.2.1, j.2] 0) k.2.2 from by
      simp [downBlock]]
    exact Submodule.mem_iSup_of_mem (i, j.1, k.1, k.2.2) (Submodule.subset_span ⟨_, rfl⟩)
  have hisospin : ReducesInvariantsTo (gaugeLorentzMaps repGauge repLorentz)
      (Submodule.span ℂ (Set.range fun k : Fin 2 × Fin 2 × Fin 2 × Fin 2 =>
        h.downBlockColour f f' k.1 k.2.1 k.2.2.1 k.2.2.2))
      (Submodule.span ℂ
        (Set.range fun m : Fin 2 × Fin 2 => h.downBlockIsospin f f' m.1 m.2)) := by
    refine ReducesInvariantsTo.ofSU2 ((InvariantReductionToSpan.reducesInvariantsTo_iSup
      fun m : Fin 2 × Fin 2 =>
        IsSU2FundamentalAntiFundamental.invariantReductionToSpan
          (h.isSU2FundamentalAntiFundamental_downBlockColour f f' m.1 m.2)).mono_left ?_)
    refine Submodule.span_le.2 <| Set.range_subset_iff.2 fun k =>
      Submodule.mem_iSup_of_mem (k.2.1, k.2.2.1) ?_
    rw [show h.downBlockColour f f' k.1 k.2.1 k.2.2.1 k.2.2.2
        = h.downBlockColour f f' (![k.2.2.2, k.1] 1) k.2.1 k.2.2.1 (![k.2.2.2, k.1] 0)
        from by simp]
    exact Submodule.subset_span ⟨_, rfl⟩
  exact (hcolour.trans hisospin).trans (ReducesInvariantsTo.ofLorentz
    ((IsBiDualRightWeyl.invariantReductionToSpan
      (h.isBiDualRightWeyl_downBlockIsospin f f')).reducesInvariantsTo.mono_left
        (range_ofPairComponents (k := .downR) (k' := .downR) (h.downBlockIsospin f f')).ge))

include h in
/-- The up-type block reduces to the up-type Yukawa term. Isospin is contracted by the
  antisymmetric symbol here, the Higgs symbol and the quark doublet both carrying the
  anti-fundamental. -/
lemma reducesInvariantsTo_upYukawa (f f' : Fin 3) :
    ReducesInvariantsTo (gaugeLorentzMaps repGauge repLorentz) (h.upBlockSubmodule f f')
      (ℂ ∙ h.upYukawa f f') := by
  have hcolour : ReducesInvariantsTo (gaugeLorentzMaps repGauge repLorentz)
      (h.upBlockSubmodule f f')
      (Submodule.span ℂ (Set.range fun k : Fin 2 × Fin 2 × Fin 2 × Fin 2 =>
        h.upBlockColour f f' k.1 k.2.1 k.2.2.1 k.2.2.2)) := by
    refine ReducesInvariantsTo.ofSU3 ((InvariantReductionToSpan.reducesInvariantsTo_iSup
      fun k : Fin 2 × Fin 2 × Fin 2 × Fin 2 =>
        IsSU3FundamentalAntiFundamental.invariantReductionToSpan
          (h.isSU3FundamentalAntiFundamental_upBlock f f' k.1 k.2.1 k.2.2.1 k.2.2.2)).mono_left ?_)
    rw [upBlockSubmodule]
    refine Submodule.mul_mul_le_of_le_span_range h.higgsSubmodule_zero_le
      (le_of_eq (h.range_baru_eq f)) (le_of_eq (h.range_Q_eq f')) fun i j k => ?_
    rw [show h.isHiggsSector.higgs ![] i * (h.isFermionSector.baruComponent f ![] j *
        h.isFermionSector.QComponent f' ![] k)
        = h.upBlock f f' i j.1 (![j.2, k.2.1] 0) k.1 (![j.2, k.2.1] 1) k.2.2 from by
      simp [upBlock]]
    exact Submodule.mem_iSup_of_mem (i, j.1, k.1, k.2.2) (Submodule.subset_span ⟨_, rfl⟩)
  have hisospin : ReducesInvariantsTo (gaugeLorentzMaps repGauge repLorentz)
      (Submodule.span ℂ (Set.range fun k : Fin 2 × Fin 2 × Fin 2 × Fin 2 =>
        h.upBlockColour f f' k.1 k.2.1 k.2.2.1 k.2.2.2))
      (Submodule.span ℂ
        (Set.range fun m : Fin 2 × Fin 2 => h.upBlockIsospin f f' m.1 m.2)) := by
    refine ReducesInvariantsTo.ofSU2 ((InvariantReductionToSpan.reducesInvariantsTo_iSup
      fun m : Fin 2 × Fin 2 =>
        IsSU2BiAntiFundamental.invariantReductionToSpan
          (h.isSU2BiAntiFundamental_upBlockColour f f' m.1 m.2)).mono_left ?_)
    refine Submodule.span_le.2 <| Set.range_subset_iff.2 fun k =>
      Submodule.mem_iSup_of_mem (k.2.1, k.2.2.1) ?_
    rw [show h.upBlockColour f f' k.1 k.2.1 k.2.2.1 k.2.2.2
        = h.upBlockColour f f' (![k.1, k.2.2.2] 0) k.2.1 k.2.2.1 (![k.1, k.2.2.2] 1)
        from by simp]
    exact Submodule.subset_span ⟨_, rfl⟩
  exact (hcolour.trans hisospin).trans (ReducesInvariantsTo.ofLorentz
    ((IsBiDualLeftWeyl.invariantReductionToSpan
      (h.isBiDualLeftWeyl_upBlockIsospin f f')).reducesInvariantsTo.mono_left
        (range_ofPairComponents (k := .downL) (k' := .downL) (h.upBlockIsospin f f')).ge))

include h in
/-- The charged-lepton block reduces to the charged-lepton Yukawa term. Its colour stage is
  the trivial one: the three symbols carry no colour index between them, so the block is
  fixed by the colour factor and the stage reduces it to itself. -/
lemma reducesInvariantsTo_leptonYukawa (f f' : Fin 3) :
    ReducesInvariantsTo (gaugeLorentzMaps repGauge repLorentz) (h.leptonBlockSubmodule f f')
      (ℂ ∙ h.leptonYukawa f f') := by
  have hcolour : ReducesInvariantsTo (gaugeLorentzMaps repGauge repLorentz)
      (h.leptonBlockSubmodule f f')
      (Submodule.span ℂ (Set.range fun k : Fin 2 × Fin 2 × Fin 2 × Fin 2 =>
        h.leptonBlock f f' k.1 k.2.1 k.2.2.1 k.2.2.2)) := by
    refine ReducesInvariantsTo.ofSU3 ((InvariantReductionToSpan.reducesInvariantsTo_iSup
      fun k : Fin 2 × Fin 2 × Fin 2 × Fin 2 =>
        InvariantReductionToSpan.ofFixed (h.leptonBlock f f' k.1 k.2.1 k.2.2.1 k.2.2.2)
          fun U => h.repGauge_su3_leptonBlock U f f' k.1 k.2.1 k.2.2.1 k.2.2.2).mono_left ?_)
    rw [leptonBlockSubmodule]
    refine Submodule.mul_mul_le_of_le_span_range h.higgsSubmodule_zero_le
      (le_of_eq (h.range_barL_eq f)) (le_of_eq (h.range_e_eq f')) fun i j k => ?_
    rw [show h.isHiggsSector.higgs ![] i * (h.isFermionSector.barLComponent f ![] j *
        h.isFermionSector.eComponent f' ![] k)
        = h.leptonBlock f f' i j.1 j.2 k from by simp [leptonBlock]]
    exact Submodule.mem_iSup_of_mem (i, j.1, j.2, k) (Submodule.mem_span_singleton_self _)
  have hisospin : ReducesInvariantsTo (gaugeLorentzMaps repGauge repLorentz)
      (Submodule.span ℂ (Set.range fun k : Fin 2 × Fin 2 × Fin 2 × Fin 2 =>
        h.leptonBlock f f' k.1 k.2.1 k.2.2.1 k.2.2.2))
      (Submodule.span ℂ
        (Set.range fun m : Fin 2 × Fin 2 => h.leptonBlockIsospin f f' m.1 m.2)) := by
    refine ReducesInvariantsTo.ofSU2 ((InvariantReductionToSpan.reducesInvariantsTo_iSup
      fun m : Fin 2 × Fin 2 =>
        IsSU2FundamentalAntiFundamental.invariantReductionToSpan
          (h.isSU2FundamentalAntiFundamental_leptonBlock f f' m.1 m.2)).mono_left ?_)
    refine Submodule.span_le.2 <| Set.range_subset_iff.2 fun k =>
      Submodule.mem_iSup_of_mem (k.2.1, k.2.2.2) ?_
    rw [show h.leptonBlock f f' k.1 k.2.1 k.2.2.1 k.2.2.2
        = h.leptonBlock f f' (![k.2.2.1, k.1] 1) k.2.1 (![k.2.2.1, k.1] 0) k.2.2.2
        from by simp]
    exact Submodule.subset_span ⟨_, rfl⟩
  exact (hcolour.trans hisospin).trans (ReducesInvariantsTo.ofLorentz
    ((IsBiDualRightWeyl.invariantReductionToSpan
      (h.isBiDualRightWeyl_leptonBlockIsospin f f')).reducesInvariantsTo.mono_left
        (range_ofPairComponents (k := .downR) (k' := .downR) (h.leptonBlockIsospin f f')).ge))

include h in
/-- The conjugate down-type block reduces to the conjugate down-type Yukawa term. -/
lemma reducesInvariantsTo_barDownYukawa (f f' : Fin 3) :
    ReducesInvariantsTo (gaugeLorentzMaps repGauge repLorentz) (h.barDownBlockSubmodule f f')
      (ℂ ∙ h.barDownYukawa f f') := by
  have hcolour : ReducesInvariantsTo (gaugeLorentzMaps repGauge repLorentz)
      (h.barDownBlockSubmodule f f')
      (Submodule.span ℂ (Set.range fun k : Fin 2 × Fin 2 × Fin 2 × Fin 2 =>
        h.barDownBlockColour f f' k.1 k.2.1 k.2.2.1 k.2.2.2)) := by
    refine ReducesInvariantsTo.ofSU3 ((InvariantReductionToSpan.reducesInvariantsTo_iSup
      fun k : Fin 2 × Fin 2 × Fin 2 × Fin 2 =>
        IsSU3FundamentalAntiFundamental.invariantReductionToSpan
          (h.isSU3FundamentalAntiFundamental_barDownBlock f f' k.1 k.2.1 k.2.2.1
            k.2.2.2)).mono_left ?_)
    rw [barDownBlockSubmodule]
    refine Submodule.mul_mul_le_of_le_span_range h.barHiggsSubmodule_zero_le
      (le_of_eq (h.range_bard_eq f)) (le_of_eq (h.range_Q_eq f')) fun i j k => ?_
    rw [show h.isHiggsSector.barHiggs ![] i * (h.isFermionSector.bardComponent f ![] j *
        h.isFermionSector.QComponent f' ![] k)
        = h.barDownBlock f f' i j.1 (![j.2, k.2.1] 0) k.1 (![j.2, k.2.1] 1) k.2.2 from by
      simp [barDownBlock]]
    exact Submodule.mem_iSup_of_mem (i, j.1, k.1, k.2.2) (Submodule.subset_span ⟨_, rfl⟩)
  have hisospin : ReducesInvariantsTo (gaugeLorentzMaps repGauge repLorentz)
      (Submodule.span ℂ (Set.range fun k : Fin 2 × Fin 2 × Fin 2 × Fin 2 =>
        h.barDownBlockColour f f' k.1 k.2.1 k.2.2.1 k.2.2.2))
      (Submodule.span ℂ
        (Set.range fun m : Fin 2 × Fin 2 => h.barDownBlockIsospin f f' m.1 m.2)) := by
    refine ReducesInvariantsTo.ofSU2 ((InvariantReductionToSpan.reducesInvariantsTo_iSup
      fun m : Fin 2 × Fin 2 =>
        IsSU2FundamentalAntiFundamental.invariantReductionToSpan
          (h.isSU2FundamentalAntiFundamental_barDownBlockColour f f' m.1 m.2)).mono_left ?_)
    refine Submodule.span_le.2 <| Set.range_subset_iff.2 fun k =>
      Submodule.mem_iSup_of_mem (k.2.1, k.2.2.1) ?_
    rw [show h.barDownBlockColour f f' k.1 k.2.1 k.2.2.1 k.2.2.2
        = h.barDownBlockColour f f' (![k.1, k.2.2.2] 0) k.2.1 k.2.2.1 (![k.1, k.2.2.2] 1)
        from by simp]
    exact Submodule.subset_span ⟨_, rfl⟩
  exact (hcolour.trans hisospin).trans (ReducesInvariantsTo.ofLorentz
    ((IsBiDualLeftWeyl.invariantReductionToSpan
      (h.isBiDualLeftWeyl_barDownBlockIsospin f f')).reducesInvariantsTo.mono_left
        (range_ofPairComponents (k := .downL) (k' := .downL) (h.barDownBlockIsospin f f')).ge))

include h in
/-- The conjugate up-type block reduces to the conjugate up-type Yukawa term. -/
lemma reducesInvariantsTo_barUpYukawa (f f' : Fin 3) :
    ReducesInvariantsTo (gaugeLorentzMaps repGauge repLorentz) (h.barUpBlockSubmodule f f')
      (ℂ ∙ h.barUpYukawa f f') := by
  have hcolour : ReducesInvariantsTo (gaugeLorentzMaps repGauge repLorentz)
      (h.barUpBlockSubmodule f f')
      (Submodule.span ℂ (Set.range fun k : Fin 2 × Fin 2 × Fin 2 × Fin 2 =>
        h.barUpBlockColour f f' k.1 k.2.1 k.2.2.1 k.2.2.2)) := by
    refine ReducesInvariantsTo.ofSU3 ((InvariantReductionToSpan.reducesInvariantsTo_iSup
      fun k : Fin 2 × Fin 2 × Fin 2 × Fin 2 =>
        IsSU3FundamentalAntiFundamental.invariantReductionToSpan
          (h.isSU3FundamentalAntiFundamental_barUpBlock f f' k.1 k.2.1 k.2.2.1
            k.2.2.2)).mono_left ?_)
    rw [barUpBlockSubmodule]
    refine Submodule.mul_mul_le_of_le_span_range h.barHiggsSubmodule_zero_le
      (le_of_eq (h.range_u_eq f)) (le_of_eq (h.range_barQ_eq f')) fun i j k => ?_
    rw [show h.isHiggsSector.barHiggs ![] i * (h.isFermionSector.uComponent f ![] j *
        h.isFermionSector.barQComponent f' ![] k)
        = h.barUpBlock f f' i j.1 (![k.2.1, j.2] 1) k.1 (![k.2.1, j.2] 0) k.2.2 from by
      simp [barUpBlock]]
    exact Submodule.mem_iSup_of_mem (i, j.1, k.1, k.2.2) (Submodule.subset_span ⟨_, rfl⟩)
  have hisospin : ReducesInvariantsTo (gaugeLorentzMaps repGauge repLorentz)
      (Submodule.span ℂ (Set.range fun k : Fin 2 × Fin 2 × Fin 2 × Fin 2 =>
        h.barUpBlockColour f f' k.1 k.2.1 k.2.2.1 k.2.2.2))
      (Submodule.span ℂ
        (Set.range fun m : Fin 2 × Fin 2 => h.barUpBlockIsospin f f' m.1 m.2)) := by
    refine ReducesInvariantsTo.ofSU2 ((InvariantReductionToSpan.reducesInvariantsTo_iSup
      fun m : Fin 2 × Fin 2 =>
        IsSU2BiFundamental.invariantReductionToSpan
          (h.isSU2BiFundamental_barUpBlockColour f f' m.1 m.2)).mono_left ?_)
    refine Submodule.span_le.2 <| Set.range_subset_iff.2 fun k =>
      Submodule.mem_iSup_of_mem (k.2.1, k.2.2.1) ?_
    rw [show h.barUpBlockColour f f' k.1 k.2.1 k.2.2.1 k.2.2.2
        = h.barUpBlockColour f f' (![k.1, k.2.2.2] 0) k.2.1 k.2.2.1 (![k.1, k.2.2.2] 1)
        from by simp]
    exact Submodule.subset_span ⟨_, rfl⟩
  exact (hcolour.trans hisospin).trans (ReducesInvariantsTo.ofLorentz
    ((IsBiDualRightWeyl.invariantReductionToSpan
      (h.isBiDualRightWeyl_barUpBlockIsospin f f')).reducesInvariantsTo.mono_left
        (range_ofPairComponents (k := .downR) (k' := .downR) (h.barUpBlockIsospin f f')).ge))

include h in
/-- The conjugate charged-lepton block reduces to the conjugate charged-lepton Yukawa term,
  again with the trivial colour stage. -/
lemma reducesInvariantsTo_barLeptonYukawa (f f' : Fin 3) :
    ReducesInvariantsTo (gaugeLorentzMaps repGauge repLorentz) (h.barLeptonBlockSubmodule f f')
      (ℂ ∙ h.barLeptonYukawa f f') := by
  have hcolour : ReducesInvariantsTo (gaugeLorentzMaps repGauge repLorentz)
      (h.barLeptonBlockSubmodule f f')
      (Submodule.span ℂ (Set.range fun k : Fin 2 × Fin 2 × Fin 2 × Fin 2 =>
        h.barLeptonBlock f f' k.1 k.2.1 k.2.2.1 k.2.2.2)) := by
    refine ReducesInvariantsTo.ofSU3 ((InvariantReductionToSpan.reducesInvariantsTo_iSup
      fun k : Fin 2 × Fin 2 × Fin 2 × Fin 2 =>
        InvariantReductionToSpan.ofFixed (h.barLeptonBlock f f' k.1 k.2.1 k.2.2.1 k.2.2.2)
          fun U =>
            h.repGauge_su3_barLeptonBlock U f f' k.1 k.2.1 k.2.2.1 k.2.2.2).mono_left ?_)
    rw [barLeptonBlockSubmodule]
    refine Submodule.mul_mul_le_of_le_span_range h.barHiggsSubmodule_zero_le
      (le_of_eq (h.range_L_eq f)) (le_of_eq (h.range_bare_eq f')) fun i j k => ?_
    rw [show h.isHiggsSector.barHiggs ![] i * (h.isFermionSector.LComponent f ![] j *
        h.isFermionSector.bareComponent f' ![] k)
        = h.barLeptonBlock f f' i j.1 j.2 k from by simp [barLeptonBlock]]
    exact Submodule.mem_iSup_of_mem (i, j.1, j.2, k) (Submodule.mem_span_singleton_self _)
  have hisospin : ReducesInvariantsTo (gaugeLorentzMaps repGauge repLorentz)
      (Submodule.span ℂ (Set.range fun k : Fin 2 × Fin 2 × Fin 2 × Fin 2 =>
        h.barLeptonBlock f f' k.1 k.2.1 k.2.2.1 k.2.2.2))
      (Submodule.span ℂ
        (Set.range fun m : Fin 2 × Fin 2 => h.barLeptonBlockIsospin f f' m.1 m.2)) := by
    refine ReducesInvariantsTo.ofSU2 ((InvariantReductionToSpan.reducesInvariantsTo_iSup
      fun m : Fin 2 × Fin 2 =>
        IsSU2FundamentalAntiFundamental.invariantReductionToSpan
          (h.isSU2FundamentalAntiFundamental_barLeptonBlock f f' m.1 m.2)).mono_left ?_)
    refine Submodule.span_le.2 <| Set.range_subset_iff.2 fun k =>
      Submodule.mem_iSup_of_mem (k.2.1, k.2.2.2) ?_
    rw [show h.barLeptonBlock f f' k.1 k.2.1 k.2.2.1 k.2.2.2
        = h.barLeptonBlock f f' (![k.1, k.2.2.1] 0) k.2.1 (![k.1, k.2.2.1] 1) k.2.2.2
        from by simp]
    exact Submodule.subset_span ⟨_, rfl⟩
  exact (hcolour.trans hisospin).trans (ReducesInvariantsTo.ofLorentz
    ((IsBiDualLeftWeyl.invariantReductionToSpan
      (h.isBiDualLeftWeyl_barLeptonBlockIsospin f f')).reducesInvariantsTo.mono_left
        (range_ofPairComponents (k := .downL) (k' := .downL) (h.barLeptonBlockIsospin f f')).ge))

/-!

## E. The classification of the invariants of mass weight eight

The two directions meet.  Forwards: the torus reduces the sector to its weight-zero piece,
the piece lies in the six block submodules, and the blocks reduce to the Yukawa span.
Backwards: `yukawaSpan_le_inf` says the Yukawa span is made of invariants of the right mass
weight to begin with, which turns the reduction into an equivalence rather than a one-way
inclusion.

-/

include h in
/-- The Yukawa span is fixed pointwise by both groups, `yukawaSpan_le_inf` placing it inside
  both spaces of invariants. -/
lemma isFixedBy_yukawaSpan : IsFixedBy (gaugeLorentzMaps repGauge repLorentz) h.yukawaSpan := by
  intro p y hy
  obtain ⟨hmem, hL⟩ := Submodule.mem_inf.1 (h.yukawaSpan_le_inf hy)
  obtain ⟨-, hG⟩ := Submodule.mem_inf.1 hmem
  cases p with
  | inl g => exact (Representation.mem_invariants _ _).1 hG g
  | inr Λ => exact (Representation.mem_invariants _ _).1 hL Λ

/-- The line through a down-type Yukawa term lies in the Yukawa span. -/
lemma span_downYukawa_le_yukawaSpan (f f' : Fin 3) :
    ℂ ∙ h.downYukawa f f' ≤ h.yukawaSpan :=
  (Submodule.span_singleton_le_iff_mem _ _).2 (Submodule.mem_sup_left (Submodule.mem_sup_left
    (Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_left
      (Submodule.mem_iSup_of_mem f (Submodule.mem_iSup_of_mem f'
        (Submodule.mem_span_singleton_self _))))))))

/-- The line through an up-type Yukawa term lies in the Yukawa span. -/
lemma span_upYukawa_le_yukawaSpan (f f' : Fin 3) :
    ℂ ∙ h.upYukawa f f' ≤ h.yukawaSpan :=
  (Submodule.span_singleton_le_iff_mem _ _).2 (Submodule.mem_sup_left (Submodule.mem_sup_left
    (Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_right
      (Submodule.mem_iSup_of_mem f (Submodule.mem_iSup_of_mem f'
        (Submodule.mem_span_singleton_self _))))))))

/-- The line through a charged-lepton Yukawa term lies in the Yukawa span. -/
lemma span_leptonYukawa_le_yukawaSpan (f f' : Fin 3) :
    ℂ ∙ h.leptonYukawa f f' ≤ h.yukawaSpan :=
  (Submodule.span_singleton_le_iff_mem _ _).2 (Submodule.mem_sup_left (Submodule.mem_sup_left
    (Submodule.mem_sup_left (Submodule.mem_sup_right
      (Submodule.mem_iSup_of_mem f (Submodule.mem_iSup_of_mem f'
        (Submodule.mem_span_singleton_self _)))))))

/-- The line through a conjugate down-type Yukawa term lies in the Yukawa span. -/
lemma span_barDownYukawa_le_yukawaSpan (f f' : Fin 3) :
    ℂ ∙ h.barDownYukawa f f' ≤ h.yukawaSpan :=
  (Submodule.span_singleton_le_iff_mem _ _).2 (Submodule.mem_sup_left (Submodule.mem_sup_left
    (Submodule.mem_sup_right (Submodule.mem_iSup_of_mem f (Submodule.mem_iSup_of_mem f'
      (Submodule.mem_span_singleton_self _))))))

/-- The line through a conjugate up-type Yukawa term lies in the Yukawa span. -/
lemma span_barUpYukawa_le_yukawaSpan (f f' : Fin 3) :
    ℂ ∙ h.barUpYukawa f f' ≤ h.yukawaSpan :=
  (Submodule.span_singleton_le_iff_mem _ _).2 (Submodule.mem_sup_left
    (Submodule.mem_sup_right (Submodule.mem_iSup_of_mem f (Submodule.mem_iSup_of_mem f'
      (Submodule.mem_span_singleton_self _)))))

/-- The line through a conjugate charged-lepton Yukawa term lies in the Yukawa span. -/
lemma span_barLeptonYukawa_le_yukawaSpan (f f' : Fin 3) :
    ℂ ∙ h.barLeptonYukawa f f' ≤ h.yukawaSpan :=
  (Submodule.span_singleton_le_iff_mem _ _).2 (Submodule.mem_sup_right
    (Submodule.mem_iSup_of_mem f (Submodule.mem_iSup_of_mem f'
      (Submodule.mem_span_singleton_self _))))

include h in
/-- The join of the six block submodules over the nine family pairs reduces to the Yukawa
  span: the fifty-four blocks are taken one at a time, each in turn joining the error term
  of the others, which is what their stability is for. -/
lemma reducesInvariantsTo_yukawaSpan :
    ReducesInvariantsTo (gaugeLorentzMaps repGauge repLorentz) h.blockSubmodule h.yukawaSpan := by
  have hW : IsStableUnder (gaugeLorentzMaps repGauge repLorentz) h.yukawaSpan :=
    h.isFixedBy_yukawaSpan.isStableUnder
  have hblock : ∀ f f' : Fin 3, ReducesInvariantsTo (gaugeLorentzMaps repGauge repLorentz)
      (h.downBlockSubmodule f f' ⊔ h.upBlockSubmodule f f' ⊔ h.leptonBlockSubmodule f f'
        ⊔ h.barDownBlockSubmodule f f' ⊔ h.barUpBlockSubmodule f f'
        ⊔ h.barLeptonBlockSubmodule f f') h.yukawaSpan := fun f f' =>
    ReducesInvariantsTo.sup (ReducesInvariantsTo.sup (ReducesInvariantsTo.sup
      (ReducesInvariantsTo.sup (ReducesInvariantsTo.sup
      ((h.reducesInvariantsTo_downYukawa f f').mono_right (h.span_downYukawa_le_yukawaSpan f f'))
      ((h.reducesInvariantsTo_upYukawa f f').mono_right (h.span_upYukawa_le_yukawaSpan f f'))
      (h.isStableUnder_upBlockSubmodule f f') hW)
      ((h.reducesInvariantsTo_leptonYukawa f f').mono_right
        (h.span_leptonYukawa_le_yukawaSpan f f'))
      (h.isStableUnder_leptonBlockSubmodule f f') hW)
      ((h.reducesInvariantsTo_barDownYukawa f f').mono_right
        (h.span_barDownYukawa_le_yukawaSpan f f'))
      (h.isStableUnder_barDownBlockSubmodule f f') hW)
      ((h.reducesInvariantsTo_barUpYukawa f f').mono_right (h.span_barUpYukawa_le_yukawaSpan f f'))
      (h.isStableUnder_barUpBlockSubmodule f f') hW)
      ((h.reducesInvariantsTo_barLeptonYukawa f f').mono_right
        (h.span_barLeptonYukawa_le_yukawaSpan f f'))
      (h.isStableUnder_barLeptonBlockSubmodule f f') hW
  have hstable : ∀ f f' : Fin 3, IsStableUnder (gaugeLorentzMaps repGauge repLorentz)
      (h.downBlockSubmodule f f' ⊔ h.upBlockSubmodule f f' ⊔ h.leptonBlockSubmodule f f'
        ⊔ h.barDownBlockSubmodule f f' ⊔ h.barUpBlockSubmodule f f'
        ⊔ h.barLeptonBlockSubmodule f f') := fun f f' =>
    ((((h.isStableUnder_downBlockSubmodule f f').sup
      (h.isStableUnder_upBlockSubmodule f f')).sup
      (h.isStableUnder_leptonBlockSubmodule f f')).sup
      (h.isStableUnder_barDownBlockSubmodule f f')).sup
      (h.isStableUnder_barUpBlockSubmodule f f') |>.sup
      (h.isStableUnder_barLeptonBlockSubmodule f f')
  rw [blockSubmodule]
  exact ReducesInvariantsTo.iSup (fun f => ReducesInvariantsTo.iSup (hblock f) (hstable f) hW)
    (fun f => isStableUnder_iSup (hstable f)) hW

include h in
/-- The Yukawa sector at mass weight eight reduces, for the gauge and Lorentz groups
  together, to the Yukawa span. Hypercharge puts an invariant in the weight-zero piece, the
  piece lies in the six block submodules, and colour, isospin and Lorentz reduce each block
  to its Yukawa term. -/
lemma reducesInvariantsTo_sectorMassWeight_higgs_fermion_eight :
    ReducesInvariantsTo (gaugeLorentzMaps repGauge repLorentz)
      (h.sectorMassWeight {GeneratorClass.higgs, GeneratorClass.fermion} 8) h.yukawaSpan :=
  (ReducesInvariantsTo.ofGauge (ReducesInvariantsTo.comp (σ := fun g : GaugeGroupI => repGauge g)
    gaugeTorusGen h.sectorMassWeightEightGaugeWeight.reducesInvariantsTo_piece_zero)).trans
    (h.reducesInvariantsTo_yukawaSpan.mono_left h.sectorMassWeightEightGaugeWeight_piece_zero_le)

include h in
/-- The classification of the Yukawa sector at mass weight eight as an equivalence: an
  element of the sector joined with a submodule `S` stable under both groups is fixed by
  both groups exactly when it is a combination of the six Yukawa couplings over the nine
  family pairs up to a remainder in `S` fixed by both groups. -/
theorem mem_sectorMassWeight_higgs_fermion_eight_sup_and_gauge_lorentz_invariant_iff
    (S : Submodule ℂ B) (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, repGauge g y ∈ S)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) (x : B) :
    (x ∈ h.sectorMassWeight {GeneratorClass.higgs, GeneratorClass.fermion} 8 ⊔ S
        ∧ (∀ g : GaugeGroupI, repGauge g x = x)
        ∧ ∀ g : SL(2,ℂ), repLorentz g x = x)
      ↔ ∃ y ∈ S, (∀ g : GaugeGroupI, repGauge g y = y)
          ∧ (∀ g : SL(2,ℂ), repLorentz g y = y)
          ∧ x - y ∈ h.yukawaSpan :=
  ReducesInvariantsTo.mem_sup_and_gauge_lorentz_invariant_iff
    h.reducesInvariantsTo_sectorMassWeight_higgs_fermion_eight
    (h.yukawaSpan_le_inf.trans (inf_le_left.trans inf_le_left)) h.isFixedBy_yukawaSpan hS hSL x

end CovAlgebraRealization

end StandardModel
