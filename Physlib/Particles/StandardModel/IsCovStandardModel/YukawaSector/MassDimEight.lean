/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.IsCovStandardModel.YukawaSector.Families.BarHiggs
public import Physlib.Particles.StandardModel.IsCovStandardModel.YukawaSector.GaugeWeightDecomposition
public import Physlib.Particles.StandardModel.Peeling
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

What is left is the peeling.  A block of the decomposition is a product of three symbol
ranges, and the classification of its invariants is three classifications in a row —
colour, then isospin, then Lorentz — each cutting the span down to the span of one
contraction.  The three groups are different, and the fifty-four surviving blocks have to
be peeled apart one at a time, so the argument is organised around a single relation
`Peels σ V W`: a `σ`-invariant of `V ⊔ S` lies in `W ⊔ S` whenever `S` is `σ`-stable.  That
relation composes — it is transitive, it is monotone in both arguments, and it is closed
under joins in its source — and every classification theorem the `GaugeGroup` and
`LorentzGroup` files provide is an instance of it, packaged as a `Step`.

## ii. Key results

- `sectorMassWeightEightGaugeWeight_piece_zero_le` : the weight-zero piece inside the six
  surviving block submodules.
- `peels_yukawaSpan` : the six blocks, over the nine family pairs, peel to the Yukawa span.
- `mem_yukawaSpan_sup_of_gauge_and_lorentz_invariant`,
  `exists_mem_of_gauge_and_lorentz_invariant` and
  `mem_sectorMassWeight_higgs_fermion_eight_sup_and_gauge_lorentz_invariant_iff` : the
  classification, in the three forms the sibling sectors state it in.

## iii. Table of contents

- A. The symbol ranges as spans of components
- B. The block submodules and their stability
- C. The twelve surviving blocks as six submodules
- D. The blocks peel to the Yukawa terms
- E. The classification of the invariants of mass weight eight

-/

@[expose] public section

namespace StandardModel

open TensorProduct Matrix MatrixGroups Lorentz Pointwise ComplexConjugate

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

## A. The symbol ranges as spans of components

-/

/-- The Higgs submodule without derivatives lies in the span of the Higgs components. -/
lemma higgsSubmodule_zero_le :
    h.isHiggsSector.higgsSubmodule 0 ≤ ⨆ i, ℂ ∙ h.isHiggsSector.higgs ![] i := by
  refine iSup_le fun l => ?_
  rw [show l = (![] : Fin 0 → Fin 1 ⊕ Fin 3) from Subsingleton.elim _ _,
    range_eq_iSup_span_dualBasis HiggsVec.orthonormBasis.toBasis (H ![])]
  exact le_rfl

/-- The conjugate Higgs submodule without derivatives lies in the span of the conjugate
  Higgs components. -/
lemma barHiggsSubmodule_zero_le :
    h.isHiggsSector.barHiggsSubmodule 0 ≤ ⨆ i, ℂ ∙ h.isHiggsSector.barHiggs ![] i := by
  refine iSup_le fun l => ?_
  rw [show l = (![] : Fin 0 → Fin 1 ⊕ Fin 3) from Subsingleton.elim _ _,
    range_eq_iSup_span_dualBasis HiggsVec.orthonormBasis.toBasis.conj (barH ![])]
  exact le_rfl

/-- The range of the down-singlet symbol map is the span of its components. -/
lemma range_d_eq (f : Fin 3) :
    LinearMap.range (d f (![] : Fin 0 → Fin 1 ⊕ Fin 3))
      = ⨆ j, ℂ ∙ h.isFermionSector.dComponent f ![] j :=
  range_eq_iSup_span_dualBasis DownSinglet.basis (d f ![])

/-- The range of the conjugate down-singlet symbol map is the span of its components. -/
lemma range_bard_eq (f : Fin 3) :
    LinearMap.range (bard f (![] : Fin 0 → Fin 1 ⊕ Fin 3))
      = ⨆ j, ℂ ∙ h.isFermionSector.bardComponent f ![] j :=
  range_eq_iSup_span_dualBasis DownSinglet.basis.conj (bard f ![])

/-- The range of the up-singlet symbol map is the span of its components. -/
lemma range_u_eq (f : Fin 3) :
    LinearMap.range (u f (![] : Fin 0 → Fin 1 ⊕ Fin 3))
      = ⨆ j, ℂ ∙ h.isFermionSector.uComponent f ![] j :=
  range_eq_iSup_span_dualBasis UpSinglet.basis (u f ![])

/-- The range of the conjugate up-singlet symbol map is the span of its components. -/
lemma range_baru_eq (f : Fin 3) :
    LinearMap.range (baru f (![] : Fin 0 → Fin 1 ⊕ Fin 3))
      = ⨆ j, ℂ ∙ h.isFermionSector.baruComponent f ![] j :=
  range_eq_iSup_span_dualBasis UpSinglet.basis.conj (baru f ![])

/-- The range of the quark-doublet symbol map is the span of its components. -/
lemma range_Q_eq (f : Fin 3) :
    LinearMap.range (Q f (![] : Fin 0 → Fin 1 ⊕ Fin 3))
      = ⨆ j, ℂ ∙ h.isFermionSector.QComponent f ![] j :=
  range_eq_iSup_span_dualBasis QuarkDoublet.basis (Q f ![])

/-- The range of the conjugate quark-doublet symbol map is the span of its components. -/
lemma range_barQ_eq (f : Fin 3) :
    LinearMap.range (barQ f (![] : Fin 0 → Fin 1 ⊕ Fin 3))
      = ⨆ j, ℂ ∙ h.isFermionSector.barQComponent f ![] j :=
  range_eq_iSup_span_dualBasis QuarkDoublet.basis.conj (barQ f ![])

/-- The range of the lepton-doublet symbol map is the span of its components. -/
lemma range_L_eq (f : Fin 3) :
    LinearMap.range (L f (![] : Fin 0 → Fin 1 ⊕ Fin 3))
      = ⨆ j, ℂ ∙ h.isFermionSector.LComponent f ![] j :=
  range_eq_iSup_span_dualBasis LeptonDoublet.basis (L f ![])

/-- The range of the conjugate lepton-doublet symbol map is the span of its components. -/
lemma range_barL_eq (f : Fin 3) :
    LinearMap.range (barL f (![] : Fin 0 → Fin 1 ⊕ Fin 3))
      = ⨆ j, ℂ ∙ h.isFermionSector.barLComponent f ![] j :=
  range_eq_iSup_span_dualBasis LeptonDoublet.basis.conj (barL f ![])

/-- The range of the lepton-singlet symbol map is the span of its components. -/
lemma range_e_eq (f : Fin 3) :
    LinearMap.range (e f (![] : Fin 0 → Fin 1 ⊕ Fin 3))
      = ⨆ j, ℂ ∙ h.isFermionSector.eComponent f ![] j :=
  range_eq_iSup_span_dualBasis LeptonSinglet.basis (e f ![])

/-- The range of the conjugate lepton-singlet symbol map is the span of its components. -/
lemma range_bare_eq (f : Fin 3) :
    LinearMap.range (bare f (![] : Fin 0 → Fin 1 ⊕ Fin 3))
      = ⨆ j, ℂ ∙ h.isFermionSector.bareComponent f ![] j :=
  range_eq_iSup_span_dualBasis LeptonSinglet.basis.conj (bare f ![])

/-!

## B. The block submodules and their stability

A surviving block of the decomposition is the product of a Higgs range with two fermion
ranges, and this is the submodule the classification of that block runs inside.  All six
are carried into themselves by both groups, each factor being the range of an equivariant
symbol map with no derivative slots for the Lorentz group to mix, and a product of stable
submodules being stable.  That stability is what lets the six blocks — fifty-four of them
once the family pairs are counted — be peeled apart one at a time, each in turn joining the
error term of the others.

-/

include h in
/-- The two groups act on the algebra by algebra maps. -/
lemma gaugeLorentzMaps_mul (p : GaugeGroupI ⊕ SL(2,ℂ)) (a b : B) :
    gaugeLorentzMaps repGauge repLorentz p (a * b)
      = gaugeLorentzMaps repGauge repLorentz p a * gaugeLorentzMaps repGauge repLorentz p b := by
  cases p with
  | inl g => exact h.isHiggsSector.rep_mul g a b
  | inr Λ => exact h.isHiggsSector.repLorentz_mul Λ a b

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
      (LinearMap.range (d f (![] : Fin 0 → Fin 1 ⊕ Fin 3))) :=
  isStableUnder_gaugeLorentzMaps_iff.2
    ⟨isStableUnder_range_repGauge fun g φ => h.isFermionSector.repGauge_d g f ![] φ,
      fun Λ => isStableUnder_range_repLorentz (h.isFermionSector.repLorentz_d f) Λ⟩

include h in
/-- The range of the conjugate down-singlet symbol map is carried into itself by both
  groups. -/
lemma isStableUnder_range_bard (f : Fin 3) :
    IsStableUnder (gaugeLorentzMaps repGauge repLorentz)
      (LinearMap.range (bard f (![] : Fin 0 → Fin 1 ⊕ Fin 3))) :=
  isStableUnder_gaugeLorentzMaps_iff.2
    ⟨isStableUnder_range_repGauge fun g φ => h.isFermionSector.repGauge_bard g f ![] φ,
      fun Λ => isStableUnder_range_repLorentz (h.isFermionSector.repLorentz_bard f) Λ⟩

include h in
/-- The range of the up-singlet symbol map is carried into itself by both groups. -/
lemma isStableUnder_range_u (f : Fin 3) :
    IsStableUnder (gaugeLorentzMaps repGauge repLorentz)
      (LinearMap.range (u f (![] : Fin 0 → Fin 1 ⊕ Fin 3))) :=
  isStableUnder_gaugeLorentzMaps_iff.2
    ⟨isStableUnder_range_repGauge fun g φ => h.isFermionSector.repGauge_u g f ![] φ,
      fun Λ => isStableUnder_range_repLorentz (h.isFermionSector.repLorentz_u f) Λ⟩

include h in
/-- The range of the conjugate up-singlet symbol map is carried into itself by both
  groups. -/
lemma isStableUnder_range_baru (f : Fin 3) :
    IsStableUnder (gaugeLorentzMaps repGauge repLorentz)
      (LinearMap.range (baru f (![] : Fin 0 → Fin 1 ⊕ Fin 3))) :=
  isStableUnder_gaugeLorentzMaps_iff.2
    ⟨isStableUnder_range_repGauge fun g φ => h.isFermionSector.repGauge_baru g f ![] φ,
      fun Λ => isStableUnder_range_repLorentz (h.isFermionSector.repLorentz_baru f) Λ⟩

include h in
/-- The range of the quark-doublet symbol map is carried into itself by both groups. -/
lemma isStableUnder_range_Q (f : Fin 3) :
    IsStableUnder (gaugeLorentzMaps repGauge repLorentz)
      (LinearMap.range (Q f (![] : Fin 0 → Fin 1 ⊕ Fin 3))) :=
  isStableUnder_gaugeLorentzMaps_iff.2
    ⟨isStableUnder_range_repGauge fun g φ => h.isFermionSector.repGauge_Q g f ![] φ,
      fun Λ => isStableUnder_range_repLorentz (h.isFermionSector.repLorentz_Q f) Λ⟩

include h in
/-- The range of the conjugate quark-doublet symbol map is carried into itself by both
  groups. -/
lemma isStableUnder_range_barQ (f : Fin 3) :
    IsStableUnder (gaugeLorentzMaps repGauge repLorentz)
      (LinearMap.range (barQ f (![] : Fin 0 → Fin 1 ⊕ Fin 3))) :=
  isStableUnder_gaugeLorentzMaps_iff.2
    ⟨isStableUnder_range_repGauge fun g φ => h.isFermionSector.repGauge_barQ g f ![] φ,
      fun Λ => isStableUnder_range_repLorentz (h.isFermionSector.repLorentz_barQ f) Λ⟩

include h in
/-- The range of the lepton-doublet symbol map is carried into itself by both groups. -/
lemma isStableUnder_range_L (f : Fin 3) :
    IsStableUnder (gaugeLorentzMaps repGauge repLorentz)
      (LinearMap.range (L f (![] : Fin 0 → Fin 1 ⊕ Fin 3))) :=
  isStableUnder_gaugeLorentzMaps_iff.2
    ⟨isStableUnder_range_repGauge fun g φ => h.isFermionSector.repGauge_L g f ![] φ,
      fun Λ => isStableUnder_range_repLorentz (h.isFermionSector.repLorentz_L f) Λ⟩

include h in
/-- The range of the conjugate lepton-doublet symbol map is carried into itself by both
  groups. -/
lemma isStableUnder_range_barL (f : Fin 3) :
    IsStableUnder (gaugeLorentzMaps repGauge repLorentz)
      (LinearMap.range (barL f (![] : Fin 0 → Fin 1 ⊕ Fin 3))) :=
  isStableUnder_gaugeLorentzMaps_iff.2
    ⟨isStableUnder_range_repGauge fun g φ => h.isFermionSector.repGauge_barL g f ![] φ,
      fun Λ => isStableUnder_range_repLorentz (h.isFermionSector.repLorentz_barL f) Λ⟩

include h in
/-- The range of the lepton-singlet symbol map is carried into itself by both groups. -/
lemma isStableUnder_range_e (f : Fin 3) :
    IsStableUnder (gaugeLorentzMaps repGauge repLorentz)
      (LinearMap.range (e f (![] : Fin 0 → Fin 1 ⊕ Fin 3))) :=
  isStableUnder_gaugeLorentzMaps_iff.2
    ⟨isStableUnder_range_repGauge fun g φ => h.isFermionSector.repGauge_e g f ![] φ,
      fun Λ => isStableUnder_range_repLorentz (h.isFermionSector.repLorentz_e f) Λ⟩

include h in
/-- The range of the conjugate lepton-singlet symbol map is carried into itself by both
  groups. -/
lemma isStableUnder_range_bare (f : Fin 3) :
    IsStableUnder (gaugeLorentzMaps repGauge repLorentz)
      (LinearMap.range (bare f (![] : Fin 0 → Fin 1 ⊕ Fin 3))) :=
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
  h.isHiggsSector.higgsSubmodule 0 * (LinearMap.range (d f (![] : Fin 0 → Fin 1 ⊕ Fin 3))
    * LinearMap.range (barQ f' (![] : Fin 0 → Fin 1 ⊕ Fin 3)))

/-- The submodule of the up-type block `H baru Q` of a family pair. -/
noncomputable def upBlockSubmodule (f f' : Fin 3) : Submodule ℂ B :=
  h.isHiggsSector.higgsSubmodule 0 * (LinearMap.range (baru f (![] : Fin 0 → Fin 1 ⊕ Fin 3))
    * LinearMap.range (Q f' (![] : Fin 0 → Fin 1 ⊕ Fin 3)))

/-- The submodule of the charged-lepton block `H barL e` of a family pair. -/
noncomputable def leptonBlockSubmodule (f f' : Fin 3) : Submodule ℂ B :=
  h.isHiggsSector.higgsSubmodule 0 * (LinearMap.range (barL f (![] : Fin 0 → Fin 1 ⊕ Fin 3))
    * LinearMap.range (e f' (![] : Fin 0 → Fin 1 ⊕ Fin 3)))

/-- The submodule of the conjugate down-type block `barH bard Q` of a family pair. -/
noncomputable def barDownBlockSubmodule (f f' : Fin 3) : Submodule ℂ B :=
  h.isHiggsSector.barHiggsSubmodule 0
    * (LinearMap.range (bard f (![] : Fin 0 → Fin 1 ⊕ Fin 3))
      * LinearMap.range (Q f' (![] : Fin 0 → Fin 1 ⊕ Fin 3)))

/-- The submodule of the conjugate up-type block `barH u barQ` of a family pair. -/
noncomputable def barUpBlockSubmodule (f f' : Fin 3) : Submodule ℂ B :=
  h.isHiggsSector.barHiggsSubmodule 0
    * (LinearMap.range (u f (![] : Fin 0 → Fin 1 ⊕ Fin 3))
      * LinearMap.range (barQ f' (![] : Fin 0 → Fin 1 ⊕ Fin 3)))

/-- The submodule of the conjugate charged-lepton block `barH L bare` of a family pair. -/
noncomputable def barLeptonBlockSubmodule (f f' : Fin 3) : Submodule ℂ B :=
  h.isHiggsSector.barHiggsSubmodule 0
    * (LinearMap.range (L f (![] : Fin 0 → Fin 1 ⊕ Fin 3))
      * LinearMap.range (bare f' (![] : Fin 0 → Fin 1 ⊕ Fin 3)))

/-- The down-type block submodule is carried into itself by both groups. -/
lemma isStableUnder_downBlockSubmodule (f f' : Fin 3) :
    IsStableUnder (gaugeLorentzMaps repGauge repLorentz) (h.downBlockSubmodule f f') :=
  IsStableUnder.mul h.gaugeLorentzMaps_mul h.isStableUnder_higgsSubmodule_zero
    (IsStableUnder.mul h.gaugeLorentzMaps_mul (h.isStableUnder_range_d f)
      (h.isStableUnder_range_barQ f'))

/-- The up-type block submodule is carried into itself by both groups. -/
lemma isStableUnder_upBlockSubmodule (f f' : Fin 3) :
    IsStableUnder (gaugeLorentzMaps repGauge repLorentz) (h.upBlockSubmodule f f') :=
  IsStableUnder.mul h.gaugeLorentzMaps_mul h.isStableUnder_higgsSubmodule_zero
    (IsStableUnder.mul h.gaugeLorentzMaps_mul (h.isStableUnder_range_baru f)
      (h.isStableUnder_range_Q f'))

/-- The charged-lepton block submodule is carried into itself by both groups. -/
lemma isStableUnder_leptonBlockSubmodule (f f' : Fin 3) :
    IsStableUnder (gaugeLorentzMaps repGauge repLorentz) (h.leptonBlockSubmodule f f') :=
  IsStableUnder.mul h.gaugeLorentzMaps_mul h.isStableUnder_higgsSubmodule_zero
    (IsStableUnder.mul h.gaugeLorentzMaps_mul (h.isStableUnder_range_barL f)
      (h.isStableUnder_range_e f'))

/-- The conjugate down-type block submodule is carried into itself by both groups. -/
lemma isStableUnder_barDownBlockSubmodule (f f' : Fin 3) :
    IsStableUnder (gaugeLorentzMaps repGauge repLorentz) (h.barDownBlockSubmodule f f') :=
  IsStableUnder.mul h.gaugeLorentzMaps_mul h.isStableUnder_barHiggsSubmodule_zero
    (IsStableUnder.mul h.gaugeLorentzMaps_mul (h.isStableUnder_range_bard f)
      (h.isStableUnder_range_Q f'))

/-- The conjugate up-type block submodule is carried into itself by both groups. -/
lemma isStableUnder_barUpBlockSubmodule (f f' : Fin 3) :
    IsStableUnder (gaugeLorentzMaps repGauge repLorentz) (h.barUpBlockSubmodule f f') :=
  IsStableUnder.mul h.gaugeLorentzMaps_mul h.isStableUnder_barHiggsSubmodule_zero
    (IsStableUnder.mul h.gaugeLorentzMaps_mul (h.isStableUnder_range_u f)
      (h.isStableUnder_range_barQ f'))

/-- The conjugate charged-lepton block submodule is carried into itself by both groups. -/
lemma isStableUnder_barLeptonBlockSubmodule (f f' : Fin 3) :
    IsStableUnder (gaugeLorentzMaps repGauge repLorentz) (h.barLeptonBlockSubmodule f f') :=
  IsStableUnder.mul h.gaugeLorentzMaps_mul h.isStableUnder_barHiggsSubmodule_zero
    (IsStableUnder.mul h.gaugeLorentzMaps_mul (h.isStableUnder_range_L f)
      (h.isStableUnder_range_bare f'))

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

## D. The blocks peel to the Yukawa terms

Each block is classified in three stages, and each stage is the same move: one index law
holds at every value of the indices it does not see, so a family of steps is applied at
once by `Peels.iSup_step`, and what comes out is the span of the contractions, which is the
source of the next stage.  Colour first, then isospin, then Lorentz — the order is forced,
each contraction being a spectator of the ones after it.

The two lepton blocks have no colour index at all, so their first stage is `Step.ofFixed`
rather than a classification: the block is already fixed by the colour factor and the stage
peels it to itself.  That keeps them in the same three-stage shape as the four quark
blocks.

-/

include h in
/-- The down-type block peels to the down-type Yukawa term. -/
lemma peels_downYukawa (f f' : Fin 3) :
    Peels (gaugeLorentzMaps repGauge repLorentz) (h.downBlockSubmodule f f')
      (ℂ ∙ h.downYukawa f f') := by
  have hcolour : Peels (gaugeLorentzMaps repGauge repLorentz) (h.downBlockSubmodule f f')
      (⨆ k : Fin 2 × Fin 2 × Fin 2 × Fin 2,
        ℂ ∙ h.downBlockColour f f' k.1 k.2.1 k.2.2.1 k.2.2.2) := by
    refine Peels.ofSU3 ((Peels.iSup_step fun k : Fin 2 × Fin 2 × Fin 2 × Fin 2 =>
      Step.ofSU3FunAntiFun
        (h.isSU3FunAntiFun_downBlock f f' k.1 k.2.1 k.2.2.1 k.2.2.2)).mono_left ?_)
    rw [downBlockSubmodule]
    refine mul_mul_le_of_le h.higgsSubmodule_zero_le (le_of_eq (h.range_d_eq f))
      (le_of_eq (h.range_barQ_eq f')) fun i j k => ?_
    rw [show h.isHiggsSector.higgs ![] i * (h.isFermionSector.dComponent f ![] j *
        h.isFermionSector.barQComponent f' ![] k)
        = h.downBlock f f' i j.1 (![k.2.1, j.2] 1) k.1 (![k.2.1, j.2] 0) k.2.2 from by
      simp [downBlock]]
    exact Submodule.mem_iSup_of_mem (i, j.1, k.1, k.2.2) (IsSU3FunAntiFun.mem_span _)
  have hisospin : Peels (gaugeLorentzMaps repGauge repLorentz)
      (⨆ k : Fin 2 × Fin 2 × Fin 2 × Fin 2,
        ℂ ∙ h.downBlockColour f f' k.1 k.2.1 k.2.2.1 k.2.2.2)
      (⨆ m : Fin 2 × Fin 2, ℂ ∙ h.downBlockIsospin f f' m.1 m.2) := by
    refine Peels.ofSU2 ((Peels.iSup_step fun m : Fin 2 × Fin 2 =>
      Step.ofSU2FunAntiFun (h.isSU2FunAntiFun_downBlockColour f f' m.1 m.2)).mono_left ?_)
    refine iSup_le fun k => (Submodule.span_singleton_le_iff_mem _ _).2
      (Submodule.mem_iSup_of_mem (k.2.1, k.2.2.1) ?_)
    rw [show h.downBlockColour f f' k.1 k.2.1 k.2.2.1 k.2.2.2
        = h.downBlockColour f f' (![k.2.2.2, k.1] 1) k.2.1 k.2.2.1 (![k.2.2.2, k.1] 0)
        from by simp]
    exact IsSU2BiFundamental.mem_span _
  exact (hcolour.trans hisospin).trans (Peels.ofLorentz
    (Step.ofBiDualRightWeyl (h.isBiDualRightWeyl_downBlockIsospin f f')).peels)

include h in
/-- The up-type block peels to the up-type Yukawa term. Isospin is contracted by the
  antisymmetric symbol here, the Higgs symbol and the quark doublet both carrying the
  anti-fundamental. -/
lemma peels_upYukawa (f f' : Fin 3) :
    Peels (gaugeLorentzMaps repGauge repLorentz) (h.upBlockSubmodule f f')
      (ℂ ∙ h.upYukawa f f') := by
  have hcolour : Peels (gaugeLorentzMaps repGauge repLorentz) (h.upBlockSubmodule f f')
      (⨆ k : Fin 2 × Fin 2 × Fin 2 × Fin 2,
        ℂ ∙ h.upBlockColour f f' k.1 k.2.1 k.2.2.1 k.2.2.2) := by
    refine Peels.ofSU3 ((Peels.iSup_step fun k : Fin 2 × Fin 2 × Fin 2 × Fin 2 =>
      Step.ofSU3FunAntiFun
        (h.isSU3FunAntiFun_upBlock f f' k.1 k.2.1 k.2.2.1 k.2.2.2)).mono_left ?_)
    rw [upBlockSubmodule]
    refine mul_mul_le_of_le h.higgsSubmodule_zero_le (le_of_eq (h.range_baru_eq f))
      (le_of_eq (h.range_Q_eq f')) fun i j k => ?_
    rw [show h.isHiggsSector.higgs ![] i * (h.isFermionSector.baruComponent f ![] j *
        h.isFermionSector.QComponent f' ![] k)
        = h.upBlock f f' i j.1 (![j.2, k.2.1] 0) k.1 (![j.2, k.2.1] 1) k.2.2 from by
      simp [upBlock]]
    exact Submodule.mem_iSup_of_mem (i, j.1, k.1, k.2.2) (IsSU3FunAntiFun.mem_span _)
  have hisospin : Peels (gaugeLorentzMaps repGauge repLorentz)
      (⨆ k : Fin 2 × Fin 2 × Fin 2 × Fin 2,
        ℂ ∙ h.upBlockColour f f' k.1 k.2.1 k.2.2.1 k.2.2.2)
      (⨆ m : Fin 2 × Fin 2, ℂ ∙ h.upBlockIsospin f f' m.1 m.2) := by
    refine Peels.ofSU2 ((Peels.iSup_step fun m : Fin 2 × Fin 2 =>
      Step.ofSU2BiAntiFun (h.isSU2BiAntiFun_upBlockColour f f' m.1 m.2)).mono_left ?_)
    refine iSup_le fun k => (Submodule.span_singleton_le_iff_mem _ _).2
      (Submodule.mem_iSup_of_mem (k.2.1, k.2.2.1) ?_)
    rw [show h.upBlockColour f f' k.1 k.2.1 k.2.2.1 k.2.2.2
        = h.upBlockColour f f' (![k.1, k.2.2.2] 0) k.2.1 k.2.2.1 (![k.1, k.2.2.2] 1)
        from by simp]
    exact IsSU2BiFundamental.mem_span _
  exact (hcolour.trans hisospin).trans (Peels.ofLorentz
    (Step.ofBiDualLeftWeyl (h.isBiDualLeftWeyl_upBlockIsospin f f')).peels)

include h in
/-- The charged-lepton block peels to the charged-lepton Yukawa term. Its colour stage is
  the trivial one: the three symbols carry no colour index between them, so the block is
  fixed by the colour factor and the stage peels it to itself. -/
lemma peels_leptonYukawa (f f' : Fin 3) :
    Peels (gaugeLorentzMaps repGauge repLorentz) (h.leptonBlockSubmodule f f')
      (ℂ ∙ h.leptonYukawa f f') := by
  have hcolour : Peels (gaugeLorentzMaps repGauge repLorentz) (h.leptonBlockSubmodule f f')
      (⨆ k : Fin 2 × Fin 2 × Fin 2 × Fin 2,
        ℂ ∙ h.leptonBlock f f' k.1 k.2.1 k.2.2.1 k.2.2.2) := by
    refine Peels.ofSU3 ((Peels.iSup_step fun k : Fin 2 × Fin 2 × Fin 2 × Fin 2 =>
      Step.ofFixed (h.leptonBlock f f' k.1 k.2.1 k.2.2.1 k.2.2.2)
        fun U => h.repGauge_su3_leptonBlock U f f' k.1 k.2.1 k.2.2.1 k.2.2.2).mono_left ?_)
    rw [leptonBlockSubmodule]
    refine mul_mul_le_of_le h.higgsSubmodule_zero_le (le_of_eq (h.range_barL_eq f))
      (le_of_eq (h.range_e_eq f')) fun i j k => ?_
    rw [show h.isHiggsSector.higgs ![] i * (h.isFermionSector.barLComponent f ![] j *
        h.isFermionSector.eComponent f' ![] k)
        = h.leptonBlock f f' i j.1 j.2 k from by simp [leptonBlock]]
    exact Submodule.mem_iSup_of_mem (i, j.1, j.2, k) (Submodule.mem_span_singleton_self _)
  have hisospin : Peels (gaugeLorentzMaps repGauge repLorentz)
      (⨆ k : Fin 2 × Fin 2 × Fin 2 × Fin 2,
        ℂ ∙ h.leptonBlock f f' k.1 k.2.1 k.2.2.1 k.2.2.2)
      (⨆ m : Fin 2 × Fin 2, ℂ ∙ h.leptonBlockIsospin f f' m.1 m.2) := by
    refine Peels.ofSU2 ((Peels.iSup_step fun m : Fin 2 × Fin 2 =>
      Step.ofSU2FunAntiFun (h.isSU2FunAntiFun_leptonBlock f f' m.1 m.2)).mono_left ?_)
    refine iSup_le fun k => (Submodule.span_singleton_le_iff_mem _ _).2
      (Submodule.mem_iSup_of_mem (k.2.1, k.2.2.2) ?_)
    rw [show h.leptonBlock f f' k.1 k.2.1 k.2.2.1 k.2.2.2
        = h.leptonBlock f f' (![k.2.2.1, k.1] 1) k.2.1 (![k.2.2.1, k.1] 0) k.2.2.2
        from by simp]
    exact IsSU2BiFundamental.mem_span _
  exact (hcolour.trans hisospin).trans (Peels.ofLorentz
    (Step.ofBiDualRightWeyl (h.isBiDualRightWeyl_leptonBlockIsospin f f')).peels)

include h in
/-- The conjugate down-type block peels to the conjugate down-type Yukawa term. -/
lemma peels_barDownYukawa (f f' : Fin 3) :
    Peels (gaugeLorentzMaps repGauge repLorentz) (h.barDownBlockSubmodule f f')
      (ℂ ∙ h.barDownYukawa f f') := by
  have hcolour : Peels (gaugeLorentzMaps repGauge repLorentz)
      (h.barDownBlockSubmodule f f')
      (⨆ k : Fin 2 × Fin 2 × Fin 2 × Fin 2,
        ℂ ∙ h.barDownBlockColour f f' k.1 k.2.1 k.2.2.1 k.2.2.2) := by
    refine Peels.ofSU3 ((Peels.iSup_step fun k : Fin 2 × Fin 2 × Fin 2 × Fin 2 =>
      Step.ofSU3FunAntiFun
        (h.isSU3FunAntiFun_barDownBlock f f' k.1 k.2.1 k.2.2.1 k.2.2.2)).mono_left ?_)
    rw [barDownBlockSubmodule]
    refine mul_mul_le_of_le h.barHiggsSubmodule_zero_le (le_of_eq (h.range_bard_eq f))
      (le_of_eq (h.range_Q_eq f')) fun i j k => ?_
    rw [show h.isHiggsSector.barHiggs ![] i * (h.isFermionSector.bardComponent f ![] j *
        h.isFermionSector.QComponent f' ![] k)
        = h.barDownBlock f f' i j.1 (![j.2, k.2.1] 0) k.1 (![j.2, k.2.1] 1) k.2.2 from by
      simp [barDownBlock]]
    exact Submodule.mem_iSup_of_mem (i, j.1, k.1, k.2.2) (IsSU3FunAntiFun.mem_span _)
  have hisospin : Peels (gaugeLorentzMaps repGauge repLorentz)
      (⨆ k : Fin 2 × Fin 2 × Fin 2 × Fin 2,
        ℂ ∙ h.barDownBlockColour f f' k.1 k.2.1 k.2.2.1 k.2.2.2)
      (⨆ m : Fin 2 × Fin 2, ℂ ∙ h.barDownBlockIsospin f f' m.1 m.2) := by
    refine Peels.ofSU2 ((Peels.iSup_step fun m : Fin 2 × Fin 2 =>
      Step.ofSU2FunAntiFun
        (h.isSU2FunAntiFun_barDownBlockColour f f' m.1 m.2)).mono_left ?_)
    refine iSup_le fun k => (Submodule.span_singleton_le_iff_mem _ _).2
      (Submodule.mem_iSup_of_mem (k.2.1, k.2.2.1) ?_)
    rw [show h.barDownBlockColour f f' k.1 k.2.1 k.2.2.1 k.2.2.2
        = h.barDownBlockColour f f' (![k.1, k.2.2.2] 0) k.2.1 k.2.2.1 (![k.1, k.2.2.2] 1)
        from by simp]
    exact IsSU2BiFundamental.mem_span _
  exact (hcolour.trans hisospin).trans (Peels.ofLorentz
    (Step.ofBiDualLeftWeyl (h.isBiDualLeftWeyl_barDownBlockIsospin f f')).peels)

include h in
/-- The conjugate up-type block peels to the conjugate up-type Yukawa term. -/
lemma peels_barUpYukawa (f f' : Fin 3) :
    Peels (gaugeLorentzMaps repGauge repLorentz) (h.barUpBlockSubmodule f f')
      (ℂ ∙ h.barUpYukawa f f') := by
  have hcolour : Peels (gaugeLorentzMaps repGauge repLorentz) (h.barUpBlockSubmodule f f')
      (⨆ k : Fin 2 × Fin 2 × Fin 2 × Fin 2,
        ℂ ∙ h.barUpBlockColour f f' k.1 k.2.1 k.2.2.1 k.2.2.2) := by
    refine Peels.ofSU3 ((Peels.iSup_step fun k : Fin 2 × Fin 2 × Fin 2 × Fin 2 =>
      Step.ofSU3FunAntiFun
        (h.isSU3FunAntiFun_barUpBlock f f' k.1 k.2.1 k.2.2.1 k.2.2.2)).mono_left ?_)
    rw [barUpBlockSubmodule]
    refine mul_mul_le_of_le h.barHiggsSubmodule_zero_le (le_of_eq (h.range_u_eq f))
      (le_of_eq (h.range_barQ_eq f')) fun i j k => ?_
    rw [show h.isHiggsSector.barHiggs ![] i * (h.isFermionSector.uComponent f ![] j *
        h.isFermionSector.barQComponent f' ![] k)
        = h.barUpBlock f f' i j.1 (![k.2.1, j.2] 1) k.1 (![k.2.1, j.2] 0) k.2.2 from by
      simp [barUpBlock]]
    exact Submodule.mem_iSup_of_mem (i, j.1, k.1, k.2.2) (IsSU3FunAntiFun.mem_span _)
  have hisospin : Peels (gaugeLorentzMaps repGauge repLorentz)
      (⨆ k : Fin 2 × Fin 2 × Fin 2 × Fin 2,
        ℂ ∙ h.barUpBlockColour f f' k.1 k.2.1 k.2.2.1 k.2.2.2)
      (⨆ m : Fin 2 × Fin 2, ℂ ∙ h.barUpBlockIsospin f f' m.1 m.2) := by
    refine Peels.ofSU2 ((Peels.iSup_step fun m : Fin 2 × Fin 2 =>
      Step.ofSU2BiFundamental
        (h.isSU2BiFundamental_barUpBlockColour f f' m.1 m.2)).mono_left ?_)
    refine iSup_le fun k => (Submodule.span_singleton_le_iff_mem _ _).2
      (Submodule.mem_iSup_of_mem (k.2.1, k.2.2.1) ?_)
    rw [show h.barUpBlockColour f f' k.1 k.2.1 k.2.2.1 k.2.2.2
        = h.barUpBlockColour f f' (![k.1, k.2.2.2] 0) k.2.1 k.2.2.1 (![k.1, k.2.2.2] 1)
        from by simp]
    exact IsSU2BiFundamental.mem_span _
  exact (hcolour.trans hisospin).trans (Peels.ofLorentz
    (Step.ofBiDualRightWeyl (h.isBiDualRightWeyl_barUpBlockIsospin f f')).peels)

include h in
/-- The conjugate charged-lepton block peels to the conjugate charged-lepton Yukawa term,
  again with the trivial colour stage. -/
lemma peels_barLeptonYukawa (f f' : Fin 3) :
    Peels (gaugeLorentzMaps repGauge repLorentz) (h.barLeptonBlockSubmodule f f')
      (ℂ ∙ h.barLeptonYukawa f f') := by
  have hcolour : Peels (gaugeLorentzMaps repGauge repLorentz)
      (h.barLeptonBlockSubmodule f f')
      (⨆ k : Fin 2 × Fin 2 × Fin 2 × Fin 2,
        ℂ ∙ h.barLeptonBlock f f' k.1 k.2.1 k.2.2.1 k.2.2.2) := by
    refine Peels.ofSU3 ((Peels.iSup_step fun k : Fin 2 × Fin 2 × Fin 2 × Fin 2 =>
      Step.ofFixed (h.barLeptonBlock f f' k.1 k.2.1 k.2.2.1 k.2.2.2)
        fun U =>
          h.repGauge_su3_barLeptonBlock U f f' k.1 k.2.1 k.2.2.1 k.2.2.2).mono_left ?_)
    rw [barLeptonBlockSubmodule]
    refine mul_mul_le_of_le h.barHiggsSubmodule_zero_le (le_of_eq (h.range_L_eq f))
      (le_of_eq (h.range_bare_eq f')) fun i j k => ?_
    rw [show h.isHiggsSector.barHiggs ![] i * (h.isFermionSector.LComponent f ![] j *
        h.isFermionSector.bareComponent f' ![] k)
        = h.barLeptonBlock f f' i j.1 j.2 k from by simp [barLeptonBlock]]
    exact Submodule.mem_iSup_of_mem (i, j.1, j.2, k) (Submodule.mem_span_singleton_self _)
  have hisospin : Peels (gaugeLorentzMaps repGauge repLorentz)
      (⨆ k : Fin 2 × Fin 2 × Fin 2 × Fin 2,
        ℂ ∙ h.barLeptonBlock f f' k.1 k.2.1 k.2.2.1 k.2.2.2)
      (⨆ m : Fin 2 × Fin 2, ℂ ∙ h.barLeptonBlockIsospin f f' m.1 m.2) := by
    refine Peels.ofSU2 ((Peels.iSup_step fun m : Fin 2 × Fin 2 =>
      Step.ofSU2FunAntiFun (h.isSU2FunAntiFun_barLeptonBlock f f' m.1 m.2)).mono_left ?_)
    refine iSup_le fun k => (Submodule.span_singleton_le_iff_mem _ _).2
      (Submodule.mem_iSup_of_mem (k.2.1, k.2.2.2) ?_)
    rw [show h.barLeptonBlock f f' k.1 k.2.1 k.2.2.1 k.2.2.2
        = h.barLeptonBlock f f' (![k.1, k.2.2.1] 0) k.2.1 (![k.1, k.2.2.1] 1) k.2.2.2
        from by simp]
    exact IsSU2BiFundamental.mem_span _
  exact (hcolour.trans hisospin).trans (Peels.ofLorentz
    (Step.ofBiDualLeftWeyl (h.isBiDualLeftWeyl_barLeptonBlockIsospin f f')).peels)

/-!

## E. The classification of the invariants of mass weight eight

The two directions meet.  Forwards: a gauge invariant of the sector lies in the weight-zero
piece modulo `S`, the piece lies in the six block submodules, and the peeling takes those to
the Yukawa span.  Backwards: `yukawaSpan_le_inf` says the Yukawa span is made of invariants
of the right mass weight to begin with, so splitting `x` as `(x - y) + y` recovers the
hypotheses.  Nothing but that splitting is needed for the converse, which is what makes the
classification an equivalence rather than a one-way inclusion.

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
/-- The join of the six block submodules over the nine family pairs peels to the Yukawa
  span: the fifty-four blocks are taken one at a time, each in turn joining the error term
  of the others, which is what their stability is for. -/
lemma peels_yukawaSpan :
    Peels (gaugeLorentzMaps repGauge repLorentz) h.blockSubmodule h.yukawaSpan := by
  have hW : IsStableUnder (gaugeLorentzMaps repGauge repLorentz) h.yukawaSpan :=
    h.isFixedBy_yukawaSpan.isStableUnder
  have hblock : ∀ f f' : Fin 3, Peels (gaugeLorentzMaps repGauge repLorentz)
      (h.downBlockSubmodule f f' ⊔ h.upBlockSubmodule f f' ⊔ h.leptonBlockSubmodule f f'
        ⊔ h.barDownBlockSubmodule f f' ⊔ h.barUpBlockSubmodule f f'
        ⊔ h.barLeptonBlockSubmodule f f') h.yukawaSpan := fun f f' =>
    Peels.sup (Peels.sup (Peels.sup (Peels.sup (Peels.sup
      ((h.peels_downYukawa f f').mono_right (h.span_downYukawa_le_yukawaSpan f f'))
      ((h.peels_upYukawa f f').mono_right (h.span_upYukawa_le_yukawaSpan f f'))
      (h.isStableUnder_upBlockSubmodule f f') hW)
      ((h.peels_leptonYukawa f f').mono_right (h.span_leptonYukawa_le_yukawaSpan f f'))
      (h.isStableUnder_leptonBlockSubmodule f f') hW)
      ((h.peels_barDownYukawa f f').mono_right (h.span_barDownYukawa_le_yukawaSpan f f'))
      (h.isStableUnder_barDownBlockSubmodule f f') hW)
      ((h.peels_barUpYukawa f f').mono_right (h.span_barUpYukawa_le_yukawaSpan f f'))
      (h.isStableUnder_barUpBlockSubmodule f f') hW)
      ((h.peels_barLeptonYukawa f f').mono_right
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
  exact Peels.iSup (fun f => Peels.iSup (hblock f) (hstable f) hW)
    (fun f => isStableUnder_iSup (hstable f)) hW

include h in
/-- A gauge and Lorentz invariant of the Yukawa sector at mass weight eight, modulo a
  submodule `S` stable under both groups, lies in the Yukawa span joined with `S`.
  Hypercharge puts it in the weight-zero piece, the piece lies in the six block submodules,
  and colour, isospin and Lorentz peel each block down to its Yukawa term. -/
theorem mem_yukawaSpan_sup_of_gauge_and_lorentz_invariant (S : Submodule ℂ B)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, repGauge g y ∈ S)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) {x : B}
    (hx : x ∈ h.sectorMassWeight {GeneratorClass.higgs, GeneratorClass.fermion} 8 ⊔ S)
    (hGinv : ∀ g : GaugeGroupI, repGauge g x = x)
    (hLinv : ∀ g : SL(2,ℂ), repLorentz g x = x) :
    x ∈ h.yukawaSpan ⊔ S := by
  have hpiece := h.mem_sectorMassWeightEight_piece_zero_sup_of_invariant
    (fun i y hy => hS (gaugeTorusGen i) y hy) hx hGinv
  exact h.peels_yukawaSpan S (isStableUnder_gaugeLorentzMaps_iff.2 ⟨hS, hSL⟩) x
    (sup_le_sup_right h.sectorMassWeightEightGaugeWeight_piece_zero_le S hpiece)
    (forall_gaugeLorentzMaps_eq_self_iff.2 ⟨hGinv, hLinv⟩)

include h in
/-- The gauge and Lorentz invariants of the Yukawa sector at mass weight eight, modulo a
  submodule `S` stable under both groups: such an invariant is a combination of the six
  Yukawa couplings over the nine family pairs plus a remainder in `S`, and the remainder is
  invariant under both groups as well, being the difference of two invariants. -/
theorem exists_mem_of_gauge_and_lorentz_invariant (S : Submodule ℂ B)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, repGauge g y ∈ S)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) {x : B}
    (hx : x ∈ h.sectorMassWeight {GeneratorClass.higgs, GeneratorClass.fermion} 8 ⊔ S)
    (hGinv : ∀ g : GaugeGroupI, repGauge g x = x)
    (hLinv : ∀ g : SL(2,ℂ), repLorentz g x = x) :
    ∃ y ∈ S, (∀ g : GaugeGroupI, repGauge g y = y)
      ∧ (∀ g : SL(2,ℂ), repLorentz g y = y)
      ∧ x - y ∈ h.yukawaSpan := by
  obtain ⟨z, hz, y, hy, rfl⟩ := Submodule.mem_sup.1
    (h.mem_yukawaSpan_sup_of_gauge_and_lorentz_invariant S hS hSL hx hGinv hLinv)
  refine ⟨y, hy, fun g => ?_, fun g => ?_, by simpa using hz⟩
  · have hstep := hGinv g
    rw [map_add, show repGauge g z = z from h.isFixedBy_yukawaSpan (Sum.inl g) z hz,
      add_right_inj] at hstep
    exact hstep
  · have hstep := hLinv g
    rw [map_add, show repLorentz g z = z from h.isFixedBy_yukawaSpan (Sum.inr g) z hz,
      add_right_inj] at hstep
    exact hstep

include h in
/-- The classification of the Yukawa sector at mass weight eight as an equivalence: an
  element of the sector joined with a submodule `S` stable under both groups is fixed by
  both groups exactly when it is a combination of the six Yukawa couplings over the nine
  family pairs up to a remainder in `S` fixed by both groups. Forwards this is
  `exists_mem_of_gauge_and_lorentz_invariant`; backwards it splits `x` as `(x - y) + y`, the
  first summand being an invariant of the sector by `yukawaSpan_le_inf`. -/
theorem mem_sectorMassWeight_higgs_fermion_eight_sup_and_gauge_lorentz_invariant_iff
    (S : Submodule ℂ B) (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, repGauge g y ∈ S)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) (x : B) :
    (x ∈ h.sectorMassWeight {GeneratorClass.higgs, GeneratorClass.fermion} 8 ⊔ S
        ∧ (∀ g : GaugeGroupI, repGauge g x = x)
        ∧ ∀ g : SL(2,ℂ), repLorentz g x = x)
      ↔ ∃ y ∈ S, (∀ g : GaugeGroupI, repGauge g y = y)
          ∧ (∀ g : SL(2,ℂ), repLorentz g y = y)
          ∧ x - y ∈ h.yukawaSpan := by
  refine ⟨fun hx =>
    h.exists_mem_of_gauge_and_lorentz_invariant S hS hSL hx.1 hx.2.1 hx.2.2, ?_⟩
  rintro ⟨y, hyS, hyG, hyL, hxy⟩
  obtain ⟨hmem₀, hL⟩ := Submodule.mem_inf.1 (h.yukawaSpan_le_inf hxy)
  obtain ⟨hmem, hG⟩ := Submodule.mem_inf.1 hmem₀
  refine ⟨?_, fun g => ?_, fun g => ?_⟩
  · have hsum : x - y + y
        ∈ h.sectorMassWeight {GeneratorClass.higgs, GeneratorClass.fermion} 8 ⊔ S :=
      Submodule.add_mem _ (Submodule.mem_sup_left hmem) (Submodule.mem_sup_right hyS)
    simpa using hsum
  · have hstep : repGauge g (x - y + y) = x - y + y := by
      rw [map_add, (Representation.mem_invariants _ _).1 hG g, hyG g]
    simpa using hstep
  · have hstep : repLorentz g (x - y + y) = x - y + y := by
      rw [map_add, (Representation.mem_invariants _ _).1 hL g, hyL g]
    simpa using hstep

end IsCovStandardModel

end StandardModel
