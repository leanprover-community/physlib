/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.Particles.StandardModel.LocalFieldAlgebra.FermionSector.MassWeight.KineticTerms
public import Mathlib.RepresentationTheory.Invariants
/-!
# The kinetic terms at mass weight eight

The gauge and Lorentz invariants of the fermion sector at mass weight eight, the kinetic terms.

## i. Overview

Mass weight eight is the first weight at which the fermion sector carries an invariant,
and what it carries is the kinetic terms. The submodule is
`derivSubmodule 0 * derivSubmodule 1`, one underived tower against one once-derived one,
and the single derivative is exactly what mass weight six was missing. It supplies a
four-vector index, and a four-vector index together with a dotted and an undotted spinor
index has one invariant contraction, against the conjugate Pauli matrices. That
contraction is `ψ̄ σ̄^μ ∂_μ ψ`.

The classification runs the four stages every sector runs. Hypercharge first, through the
gauge weight decomposition, where `massWeightSubmoduleGaugeWeightEight_piece_zero` cuts the
hundred pairings of two fermion symbols down to the ten conjugate ones, every other
pairing having hypercharges that cannot cancel. Then colour, then isospin, then Lorentz,
one classification each, chained by the `ReducesInvariantsTo` relation of
`PhyslibAlpha.Mathematics.InvariantReduction` and supplied by the `KineticBlock` packages of
`KineticTerms`. What is left is the kinetic span: one term for each of the ten pairings and each of
the nine pairs of generations.

## ii. Key results

- `dbardPairSubmodule` and its nine companions : the submodule of each block of a generation pair.
- `kineticSpan` : the join of the kinetic terms over the ten conjugate pairings and the nine
  pairs of generations.
- `reducesInvariantsTo_kineticSpan` : the fermion sector at mass weight eight reduces to the
  kinetic span.
- `mem_massWeightSubmodule_eight_sup_and_gauge_lorentz_invariant_iff` : the classification at mass
  weight eight as an equivalence.

## iii. Table of contents

- A. Symbol ranges and their stability
- B. The block submodules
- C. The symbol ranges inside the derivative submodules, and the mass weight
- D. The kinetic span
- E. The blocks reduce to the kinetic terms
- F. The classification as an equivalence

## iv. References

* None.

-/

@[expose] public section

namespace StandardModel

open Matrix MatrixGroups Lorentz

namespace FermionSector

/-!

## A. Symbol ranges and their stability

The reduction asks two things of the submodule a block is read from: that the two groups
carry it into itself, and that it lies in the span of the block's components. Both come
from the symbol maps. A gauge transformation moves only the covector a symbol is evaluated
at, so a symbol range is gauge stable at any number of derivative slots. The Lorentz group
moves the covector too, but it also mixes the derivative slots, so an underived range is
Lorentz stable on its own while a once-derived one is stable only after joining over the
derivative direction — which is why a block submodule carries that join.

-/

/-- The join, over the derivative direction, of the ranges of a once-derived symbol map is
  carried into itself by the Lorentz group. A Lorentz transformation mixes the derivative
  slot into the other directions and moves the covector, and both stay inside the join. -/
lemma isStableUnder_iSup_range_deriv_one {M : Type} [AddCommGroup M] [Module ℂ M]
    {ρ : Representation ℂ SL(2,ℂ) M}
    {F : {n : ℕ} → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ M →ₗ[ℂ] fieldData.LocalCovFieldAlgebra}
    (hF : IsLorentzCovDerivTransforms repLorentz ρ F) (Λ : SL(2,ℂ)) :
    ∀ y ∈ (⨆ μ : Fin 1 ⊕ Fin 3, LinearMap.range (F ![μ])),
      repLorentz Λ y ∈ ⨆ μ : Fin 1 ⊕ Fin 3, LinearMap.range (F ![μ]) := by
  intro y hy
  have key : (⨆ μ : Fin 1 ⊕ Fin 3, LinearMap.range (F ![μ]))
      ≤ Submodule.comap (repLorentz Λ)
        (⨆ μ : Fin 1 ⊕ Fin 3, LinearMap.range (F ![μ])) := by
    refine iSup_le fun μ => ?_
    rintro _ ⟨φ, rfl⟩
    rw [Submodule.mem_comap, repLorentz_symbol_deriv_one hF Λ μ φ]
    exact Submodule.sum_mem _ fun ν _ => Submodule.smul_mem _ _
      (Submodule.mem_iSup_of_mem ν ⟨_, rfl⟩)
  exact key hy

/-- The range of an underived symbol map is carried into itself by both groups. -/
lemma isStableUnder_range_underived {M : Type} [AddCommGroup M] [Module ℂ M]
    {ρG : Representation ℂ GaugeGroupI M} {ρL : Representation ℂ SL(2,ℂ) M}
    {F : {n : ℕ} → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ M →ₗ[ℂ] fieldData.LocalCovFieldAlgebra}
    (hG : ∀ (g : GaugeGroupI) (φ : Module.Dual ℂ M),
      repGauge g (F (![] : Fin 0 → Fin 1 ⊕ Fin 3) φ)
        = F (![] : Fin 0 → Fin 1 ⊕ Fin 3) (ρG.dual g φ))
    (hL : IsLorentzCovDerivTransforms repLorentz ρL F) :
    IsStableUnder (gaugeLorentzMaps repGauge repLorentz)
      (LinearMap.range (F (![] : Fin 0 → Fin 1 ⊕ Fin 3))) :=
  isStableUnder_gaugeLorentzMaps_iff.2
    ⟨isStableUnder_range_repGauge hG, fun Λ => isStableUnder_range_repLorentz hL Λ⟩

/-- The join, over the derivative direction, of the ranges of a once-derived symbol map is
  carried into itself by both groups. -/
lemma isStableUnder_iSup_range_derived {M : Type} [AddCommGroup M] [Module ℂ M]
    {ρG : Representation ℂ GaugeGroupI M} {ρL : Representation ℂ SL(2,ℂ) M}
    {F : {n : ℕ} → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ M →ₗ[ℂ] fieldData.LocalCovFieldAlgebra}
    (hG : ∀ (g : GaugeGroupI) (μ : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ M),
      repGauge g (F ![μ] φ) = F ![μ] (ρG.dual g φ))
    (hL : IsLorentzCovDerivTransforms repLorentz ρL F) :
    IsStableUnder (gaugeLorentzMaps repGauge repLorentz)
      (⨆ μ : Fin 1 ⊕ Fin 3, LinearMap.range (F ![μ])) :=
  isStableUnder_gaugeLorentzMaps_iff.2
    ⟨isStableUnder_iSup fun μ => isStableUnder_range_repGauge (hG · μ),
      isStableUnder_iSup_range_deriv_one hL⟩

/-!

## B. The block submodules

Each of the ten conjugate pairings gives one submodule per pair of generations: the
underived range of one species against the once-derived ranges of its conjugate, joined
over the derivative direction so that the Lorentz group has somewhere to move it. Each is
carried into itself by both groups and lies in the span of the components of the matching
kinetic block, which is all the reduction asks.

-/

/-- The submodule of the `d ∂ bard` block of a generation pair, an underived
  down-singlet range against the once-derived conjugate down-singlet ranges,
  joined over the derivative direction. -/
noncomputable def dbardPairSubmodule (f f' : Fin 3) :
    Submodule ℂ fieldData.LocalCovFieldAlgebra :=
  LinearMap.range (d f (![] : Fin 0 → Fin 1 ⊕ Fin 3))
    * ⨆ μ : Fin 1 ⊕ Fin 3, LinearMap.range (bard f' ![μ])

/-- The `d ∂ bard` block submodule is carried into itself by both groups. -/
lemma isStableUnder_dbardPairSubmodule (f f' : Fin 3) :
    IsStableUnder (gaugeLorentzMaps repGauge repLorentz) (dbardPairSubmodule f f') := by
  rw [dbardPairSubmodule]
  exact IsStableUnder.mul (gaugeLorentzMaps_mul repGauge_mul repLorentz_mul)
    (isStableUnder_range_underived (F := d f) (fun g φ => repGauge_d g f ![] φ)
      (repLorentz_d f))
    (isStableUnder_iSup_range_derived (F := bard f')
      (fun g μ φ => repGauge_bard g f' ![μ] φ) (repLorentz_bard f'))

/-- The `d ∂ bard` block submodule lies in the span of the block's components. -/
lemma dbardPairSubmodule_le_blockSpan (f f' : Fin 3) :
    dbardPairSubmodule f f' ≤ (dbardKineticBlock f f').blockSpan := by
  rw [dbardPairSubmodule, KineticBlock.blockSpan]
  refine Submodule.mul_le_of_le_span_range
    (a := fun k => d f (![] : Fin 0 → Fin 1 ⊕ Fin 3) (DownSinglet.basis.dualBasis k))
    (b := fun k : (Fin 1 ⊕ Fin 3) × (Fin 2 × Fin 3) =>
      bard f' ![k.1] ((Basis.conj DownSinglet.basis).dualBasis k.2))
    (le_of_eq (LinearMap.range_eq_span_range_basis DownSinglet.basis.dualBasis _))
    (iSup_le fun μ => ?_) ?_
  · rw [LinearMap.range_eq_span_range_basis (Basis.conj DownSinglet.basis).dualBasis (bard f' ![μ])]
    exact Submodule.span_mono (Set.range_subset_iff.2 fun k => ⟨(μ, k), rfl⟩)
  · intro i j
    exact Submodule.mem_iSup_of_mem (j.1, (j.2.1, i.1), (0, 0))
      (Submodule.subset_span ⟨![j.2.2, i.2], by
        simp only [dbardKineticBlock, dbardBlk, dComponent, bardComponent,
          Matrix.cons_val_zero, Matrix.cons_val_one, Prod.mk.eta]⟩)

/-- The `d ∂ bard` block reduces to its kinetic term. -/
lemma reducesInvariantsTo_dbard (f f' : Fin 3) :
    ReducesInvariantsTo (gaugeLorentzMaps repGauge repLorentz) (dbardPairSubmodule f f')
      (ℂ ∙ (dbardKineticBlock f f').kineticTerm) :=
  (dbardKineticBlock f f').reducesInvariantsTo.mono_left
    (dbardPairSubmodule_le_blockSpan f f')

/-- The submodule of the `bard ∂ d` block of a generation pair, an underived
  conjugate down-singlet range against the once-derived down-singlet ranges,
  joined over the derivative direction. -/
noncomputable def barddPairSubmodule (f f' : Fin 3) :
    Submodule ℂ fieldData.LocalCovFieldAlgebra :=
  LinearMap.range (bard f (![] : Fin 0 → Fin 1 ⊕ Fin 3))
    * ⨆ μ : Fin 1 ⊕ Fin 3, LinearMap.range (d f' ![μ])

/-- The `bard ∂ d` block submodule is carried into itself by both groups. -/
lemma isStableUnder_barddPairSubmodule (f f' : Fin 3) :
    IsStableUnder (gaugeLorentzMaps repGauge repLorentz) (barddPairSubmodule f f') := by
  rw [barddPairSubmodule]
  exact IsStableUnder.mul (gaugeLorentzMaps_mul repGauge_mul repLorentz_mul)
    (isStableUnder_range_underived (F := bard f) (fun g φ => repGauge_bard g f ![] φ)
      (repLorentz_bard f))
    (isStableUnder_iSup_range_derived (F := d f')
      (fun g μ φ => repGauge_d g f' ![μ] φ) (repLorentz_d f'))

/-- The `bard ∂ d` block submodule lies in the span of the block's components. -/
lemma barddPairSubmodule_le_blockSpan (f f' : Fin 3) :
    barddPairSubmodule f f' ≤ (barddKineticBlock f f').blockSpan := by
  rw [barddPairSubmodule, KineticBlock.blockSpan]
  refine Submodule.mul_le_of_le_span_range
    (a := fun k => bard f (![] : Fin 0 → Fin 1 ⊕ Fin 3)
      ((Basis.conj DownSinglet.basis).dualBasis k))
    (b := fun k : (Fin 1 ⊕ Fin 3) × (Fin 2 × Fin 3) =>
      d f' ![k.1] (DownSinglet.basis.dualBasis k.2))
    (le_of_eq (LinearMap.range_eq_span_range_basis (Basis.conj DownSinglet.basis).dualBasis _))
    (iSup_le fun μ => ?_) ?_
  · rw [LinearMap.range_eq_span_range_basis DownSinglet.basis.dualBasis (d f' ![μ])]
    exact Submodule.span_mono (Set.range_subset_iff.2 fun k => ⟨(μ, k), rfl⟩)
  · intro i j
    exact Submodule.mem_iSup_of_mem (j.1, (i.1, j.2.1), (0, 0))
      (Submodule.subset_span ⟨![i.2, j.2.2], rfl⟩)

/-- The `bard ∂ d` block reduces to its kinetic term. -/
lemma reducesInvariantsTo_bardd (f f' : Fin 3) :
    ReducesInvariantsTo (gaugeLorentzMaps repGauge repLorentz) (barddPairSubmodule f f')
      (ℂ ∙ (barddKineticBlock f f').kineticTerm) :=
  (barddKineticBlock f f').reducesInvariantsTo.mono_left
    (barddPairSubmodule_le_blockSpan f f')

/-- The submodule of the `u ∂ baru` block of a generation pair, an underived
  up-singlet range against the once-derived conjugate up-singlet ranges,
  joined over the derivative direction. -/
noncomputable def ubaruPairSubmodule (f f' : Fin 3) :
    Submodule ℂ fieldData.LocalCovFieldAlgebra :=
  LinearMap.range (u f (![] : Fin 0 → Fin 1 ⊕ Fin 3))
    * ⨆ μ : Fin 1 ⊕ Fin 3, LinearMap.range (baru f' ![μ])

/-- The `u ∂ baru` block submodule is carried into itself by both groups. -/
lemma isStableUnder_ubaruPairSubmodule (f f' : Fin 3) :
    IsStableUnder (gaugeLorentzMaps repGauge repLorentz) (ubaruPairSubmodule f f') := by
  rw [ubaruPairSubmodule]
  exact IsStableUnder.mul (gaugeLorentzMaps_mul repGauge_mul repLorentz_mul)
    (isStableUnder_range_underived (F := u f) (fun g φ => repGauge_u g f ![] φ)
      (repLorentz_u f))
    (isStableUnder_iSup_range_derived (F := baru f')
      (fun g μ φ => repGauge_baru g f' ![μ] φ) (repLorentz_baru f'))

/-- The `u ∂ baru` block submodule lies in the span of the block's components. -/
lemma ubaruPairSubmodule_le_blockSpan (f f' : Fin 3) :
    ubaruPairSubmodule f f' ≤ (ubaruKineticBlock f f').blockSpan := by
  rw [ubaruPairSubmodule, KineticBlock.blockSpan]
  refine Submodule.mul_le_of_le_span_range
    (a := fun k => u f (![] : Fin 0 → Fin 1 ⊕ Fin 3) (UpSinglet.basis.dualBasis k))
    (b := fun k : (Fin 1 ⊕ Fin 3) × (Fin 2 × Fin 3) =>
      baru f' ![k.1] ((Basis.conj UpSinglet.basis).dualBasis k.2))
    (le_of_eq (LinearMap.range_eq_span_range_basis UpSinglet.basis.dualBasis _))
    (iSup_le fun μ => ?_) ?_
  · rw [LinearMap.range_eq_span_range_basis (Basis.conj UpSinglet.basis).dualBasis (baru f' ![μ])]
    exact Submodule.span_mono (Set.range_subset_iff.2 fun k => ⟨(μ, k), rfl⟩)
  · intro i j
    exact Submodule.mem_iSup_of_mem (j.1, (j.2.1, i.1), (0, 0))
      (Submodule.subset_span ⟨![j.2.2, i.2], by
        simp only [ubaruKineticBlock, ubaruBlk, uComponent, baruComponent,
          Matrix.cons_val_zero, Matrix.cons_val_one, Prod.mk.eta]⟩)

/-- The `u ∂ baru` block reduces to its kinetic term. -/
lemma reducesInvariantsTo_ubaru (f f' : Fin 3) :
    ReducesInvariantsTo (gaugeLorentzMaps repGauge repLorentz) (ubaruPairSubmodule f f')
      (ℂ ∙ (ubaruKineticBlock f f').kineticTerm) :=
  (ubaruKineticBlock f f').reducesInvariantsTo.mono_left
    (ubaruPairSubmodule_le_blockSpan f f')

/-- The submodule of the `baru ∂ u` block of a generation pair, an underived
  conjugate up-singlet range against the once-derived up-singlet ranges,
  joined over the derivative direction. -/
noncomputable def baruuPairSubmodule (f f' : Fin 3) :
    Submodule ℂ fieldData.LocalCovFieldAlgebra :=
  LinearMap.range (baru f (![] : Fin 0 → Fin 1 ⊕ Fin 3))
    * ⨆ μ : Fin 1 ⊕ Fin 3, LinearMap.range (u f' ![μ])

/-- The `baru ∂ u` block submodule is carried into itself by both groups. -/
lemma isStableUnder_baruuPairSubmodule (f f' : Fin 3) :
    IsStableUnder (gaugeLorentzMaps repGauge repLorentz) (baruuPairSubmodule f f') := by
  rw [baruuPairSubmodule]
  exact IsStableUnder.mul (gaugeLorentzMaps_mul repGauge_mul repLorentz_mul)
    (isStableUnder_range_underived (F := baru f) (fun g φ => repGauge_baru g f ![] φ)
      (repLorentz_baru f))
    (isStableUnder_iSup_range_derived (F := u f')
      (fun g μ φ => repGauge_u g f' ![μ] φ) (repLorentz_u f'))

/-- The `baru ∂ u` block submodule lies in the span of the block's components. -/
lemma baruuPairSubmodule_le_blockSpan (f f' : Fin 3) :
    baruuPairSubmodule f f' ≤ (baruuKineticBlock f f').blockSpan := by
  rw [baruuPairSubmodule, KineticBlock.blockSpan]
  refine Submodule.mul_le_of_le_span_range
    (a := fun k => baru f (![] : Fin 0 → Fin 1 ⊕ Fin 3) ((Basis.conj UpSinglet.basis).dualBasis k))
    (b := fun k : (Fin 1 ⊕ Fin 3) × (Fin 2 × Fin 3) =>
      u f' ![k.1] (UpSinglet.basis.dualBasis k.2))
    (le_of_eq (LinearMap.range_eq_span_range_basis (Basis.conj UpSinglet.basis).dualBasis _))
    (iSup_le fun μ => ?_) ?_
  · rw [LinearMap.range_eq_span_range_basis UpSinglet.basis.dualBasis (u f' ![μ])]
    exact Submodule.span_mono (Set.range_subset_iff.2 fun k => ⟨(μ, k), rfl⟩)
  · intro i j
    exact Submodule.mem_iSup_of_mem (j.1, (i.1, j.2.1), (0, 0))
      (Submodule.subset_span ⟨![i.2, j.2.2], rfl⟩)

/-- The `baru ∂ u` block reduces to its kinetic term. -/
lemma reducesInvariantsTo_baruu (f f' : Fin 3) :
    ReducesInvariantsTo (gaugeLorentzMaps repGauge repLorentz) (baruuPairSubmodule f f')
      (ℂ ∙ (baruuKineticBlock f f').kineticTerm) :=
  (baruuKineticBlock f f').reducesInvariantsTo.mono_left
    (baruuPairSubmodule_le_blockSpan f f')

/-- The submodule of the `Q ∂ barQ` block of a generation pair, an underived
  quark-doublet range against the once-derived conjugate quark-doublet ranges,
  joined over the derivative direction. -/
noncomputable def QbarQPairSubmodule (f f' : Fin 3) :
    Submodule ℂ fieldData.LocalCovFieldAlgebra :=
  LinearMap.range (Q f (![] : Fin 0 → Fin 1 ⊕ Fin 3))
    * ⨆ μ : Fin 1 ⊕ Fin 3, LinearMap.range (barQ f' ![μ])

/-- The `Q ∂ barQ` block submodule is carried into itself by both groups. -/
lemma isStableUnder_QbarQPairSubmodule (f f' : Fin 3) :
    IsStableUnder (gaugeLorentzMaps repGauge repLorentz) (QbarQPairSubmodule f f') := by
  rw [QbarQPairSubmodule]
  exact IsStableUnder.mul (gaugeLorentzMaps_mul repGauge_mul repLorentz_mul)
    (isStableUnder_range_underived (F := Q f) (fun g φ => repGauge_Q g f ![] φ)
      (repLorentz_Q f))
    (isStableUnder_iSup_range_derived (F := barQ f')
      (fun g μ φ => repGauge_barQ g f' ![μ] φ) (repLorentz_barQ f'))

/-- The `Q ∂ barQ` block submodule lies in the span of the block's components. -/
lemma QbarQPairSubmodule_le_blockSpan (f f' : Fin 3) :
    QbarQPairSubmodule f f' ≤ (QbarQKineticBlock f f').blockSpan := by
  rw [QbarQPairSubmodule, KineticBlock.blockSpan]
  refine Submodule.mul_le_of_le_span_range
    (a := fun k => Q f (![] : Fin 0 → Fin 1 ⊕ Fin 3) (QuarkDoublet.basis.dualBasis k))
    (b := fun k : (Fin 1 ⊕ Fin 3) × (Fin 2 × Fin 3 × Fin 2) =>
      barQ f' ![k.1] ((Basis.conj QuarkDoublet.basis).dualBasis k.2))
    (le_of_eq (LinearMap.range_eq_span_range_basis QuarkDoublet.basis.dualBasis _))
    (iSup_le fun μ => ?_) ?_
  · rw [LinearMap.range_eq_span_range_basis (Basis.conj QuarkDoublet.basis).dualBasis
    (barQ f' ![μ])]
    exact Submodule.span_mono (Set.range_subset_iff.2 fun k => ⟨(μ, k), by with_reducible rfl⟩)
  · intro i j
    exact Submodule.mem_iSup_of_mem (j.1, (i.1, j.2.1), (j.2.2.2, i.2.2))
      (Submodule.subset_span ⟨![j.2.2.1, i.2.1], by
        simp only [QbarQKineticBlock, QbarQBlk, QComponent, barQComponent,
          Matrix.cons_val_zero, Matrix.cons_val_one, Prod.mk.eta]⟩)

/-- The `Q ∂ barQ` block reduces to its kinetic term. -/
lemma reducesInvariantsTo_QbarQ (f f' : Fin 3) :
    ReducesInvariantsTo (gaugeLorentzMaps repGauge repLorentz) (QbarQPairSubmodule f f')
      (ℂ ∙ (QbarQKineticBlock f f').kineticTerm) :=
  (QbarQKineticBlock f f').reducesInvariantsTo.mono_left
    (QbarQPairSubmodule_le_blockSpan f f')

/-- The submodule of the `barQ ∂ Q` block of a generation pair, an underived
  conjugate quark-doublet range against the once-derived quark-doublet ranges,
  joined over the derivative direction. -/
noncomputable def barQQPairSubmodule (f f' : Fin 3) :
    Submodule ℂ fieldData.LocalCovFieldAlgebra :=
  LinearMap.range (barQ f (![] : Fin 0 → Fin 1 ⊕ Fin 3))
    * ⨆ μ : Fin 1 ⊕ Fin 3, LinearMap.range (Q f' ![μ])

/-- The `barQ ∂ Q` block submodule is carried into itself by both groups. -/
lemma isStableUnder_barQQPairSubmodule (f f' : Fin 3) :
    IsStableUnder (gaugeLorentzMaps repGauge repLorentz) (barQQPairSubmodule f f') := by
  rw [barQQPairSubmodule]
  exact IsStableUnder.mul (gaugeLorentzMaps_mul repGauge_mul repLorentz_mul)
    (isStableUnder_range_underived (F := barQ f) (fun g φ => repGauge_barQ g f ![] φ)
      (repLorentz_barQ f))
    (isStableUnder_iSup_range_derived (F := Q f')
      (fun g μ φ => repGauge_Q g f' ![μ] φ) (repLorentz_Q f'))

/-- The `barQ ∂ Q` block submodule lies in the span of the block's components. -/
lemma barQQPairSubmodule_le_blockSpan (f f' : Fin 3) :
    barQQPairSubmodule f f' ≤ (barQQKineticBlock f f').blockSpan := by
  rw [barQQPairSubmodule, KineticBlock.blockSpan]
  refine Submodule.mul_le_of_le_span_range
    (a := fun k => barQ f (![] : Fin 0 → Fin 1 ⊕ Fin 3)
      ((Basis.conj QuarkDoublet.basis).dualBasis k))
    (b := fun k : (Fin 1 ⊕ Fin 3) × (Fin 2 × Fin 3 × Fin 2) =>
      Q f' ![k.1] (QuarkDoublet.basis.dualBasis k.2))
    (le_of_eq (LinearMap.range_eq_span_range_basis (Basis.conj QuarkDoublet.basis).dualBasis _))
    (iSup_le fun μ => ?_) ?_
  · rw [LinearMap.range_eq_span_range_basis QuarkDoublet.basis.dualBasis (Q f' ![μ])]
    exact Submodule.span_mono (Set.range_subset_iff.2 fun k => ⟨(μ, k), rfl⟩)
  · intro i j
    exact Submodule.mem_iSup_of_mem (j.1, (j.2.1, i.1), (i.2.2, j.2.2.2))
      (Submodule.subset_span ⟨![i.2.1, j.2.2.1], by
        simp only [barQQKineticBlock, barQQBlk, barQComponent, QComponent,
          Matrix.cons_val_zero, Matrix.cons_val_one, Prod.mk.eta]⟩)

/-- The `barQ ∂ Q` block reduces to its kinetic term. -/
lemma reducesInvariantsTo_barQQ (f f' : Fin 3) :
    ReducesInvariantsTo (gaugeLorentzMaps repGauge repLorentz) (barQQPairSubmodule f f')
      (ℂ ∙ (barQQKineticBlock f f').kineticTerm) :=
  (barQQKineticBlock f f').reducesInvariantsTo.mono_left
    (barQQPairSubmodule_le_blockSpan f f')

/-- The submodule of the `L ∂ barL` block of a generation pair, an underived
  lepton-doublet range against the once-derived conjugate lepton-doublet ranges,
  joined over the derivative direction. -/
noncomputable def LbarLPairSubmodule (f f' : Fin 3) :
    Submodule ℂ fieldData.LocalCovFieldAlgebra :=
  LinearMap.range (L f (![] : Fin 0 → Fin 1 ⊕ Fin 3))
    * ⨆ μ : Fin 1 ⊕ Fin 3, LinearMap.range (barL f' ![μ])

/-- The `L ∂ barL` block submodule is carried into itself by both groups. -/
lemma isStableUnder_LbarLPairSubmodule (f f' : Fin 3) :
    IsStableUnder (gaugeLorentzMaps repGauge repLorentz) (LbarLPairSubmodule f f') := by
  rw [LbarLPairSubmodule]
  exact IsStableUnder.mul (gaugeLorentzMaps_mul repGauge_mul repLorentz_mul)
    (isStableUnder_range_underived (F := L f) (fun g φ => repGauge_L g f ![] φ)
      (repLorentz_L f))
    (isStableUnder_iSup_range_derived (F := barL f')
      (fun g μ φ => repGauge_barL g f' ![μ] φ) (repLorentz_barL f'))

/-- The `L ∂ barL` block submodule lies in the span of the block's components. -/
lemma LbarLPairSubmodule_le_blockSpan (f f' : Fin 3) :
    LbarLPairSubmodule f f' ≤ (LbarLKineticBlock f f').blockSpan := by
  rw [LbarLPairSubmodule, KineticBlock.blockSpan]
  refine Submodule.mul_le_of_le_span_range
    (a := fun k => L f (![] : Fin 0 → Fin 1 ⊕ Fin 3) (LeptonDoubletV.basis.dualBasis k))
    (b := fun k : (Fin 1 ⊕ Fin 3) × (Fin 2 × Fin 2) =>
      barL f' ![k.1] ((Basis.conj LeptonDoubletV.basis).dualBasis k.2))
    (le_of_eq (LinearMap.range_eq_span_range_basis LeptonDoubletV.basis.dualBasis _))
    (iSup_le fun μ => ?_) ?_
  · rw [LinearMap.range_eq_span_range_basis (Basis.conj LeptonDoubletV.basis).dualBasis
    (barL f' ![μ])]
    exact Submodule.span_mono (Set.range_subset_iff.2 fun k => ⟨(μ, k), by with_reducible rfl⟩)
  · intro i j
    exact Submodule.mem_iSup_of_mem (j.1, (i.1, j.2.1), (j.2.2, i.2))
      (Submodule.subset_span ⟨![0, 0], by
        simp only [LbarLKineticBlock, LbarLBlk, LComponent, barLComponent,
          Matrix.cons_val_zero, Matrix.cons_val_one, Prod.mk.eta]⟩)

/-- The `L ∂ barL` block reduces to its kinetic term. -/
lemma reducesInvariantsTo_LbarL (f f' : Fin 3) :
    ReducesInvariantsTo (gaugeLorentzMaps repGauge repLorentz) (LbarLPairSubmodule f f')
      (ℂ ∙ (LbarLKineticBlock f f').kineticTerm) :=
  (LbarLKineticBlock f f').reducesInvariantsTo.mono_left
    (LbarLPairSubmodule_le_blockSpan f f')

/-- The submodule of the `barL ∂ L` block of a generation pair, an underived
  conjugate lepton-doublet range against the once-derived lepton-doublet ranges,
  joined over the derivative direction. -/
noncomputable def barLLPairSubmodule (f f' : Fin 3) :
    Submodule ℂ fieldData.LocalCovFieldAlgebra :=
  LinearMap.range (barL f (![] : Fin 0 → Fin 1 ⊕ Fin 3))
    * ⨆ μ : Fin 1 ⊕ Fin 3, LinearMap.range (L f' ![μ])

/-- The `barL ∂ L` block submodule is carried into itself by both groups. -/
lemma isStableUnder_barLLPairSubmodule (f f' : Fin 3) :
    IsStableUnder (gaugeLorentzMaps repGauge repLorentz) (barLLPairSubmodule f f') := by
  rw [barLLPairSubmodule]
  exact IsStableUnder.mul (gaugeLorentzMaps_mul repGauge_mul repLorentz_mul)
    (isStableUnder_range_underived (F := barL f) (fun g φ => repGauge_barL g f ![] φ)
      (repLorentz_barL f))
    (isStableUnder_iSup_range_derived (F := L f')
      (fun g μ φ => repGauge_L g f' ![μ] φ) (repLorentz_L f'))

/-- The `barL ∂ L` block submodule lies in the span of the block's components. -/
lemma barLLPairSubmodule_le_blockSpan (f f' : Fin 3) :
    barLLPairSubmodule f f' ≤ (barLLKineticBlock f f').blockSpan := by
  rw [barLLPairSubmodule, KineticBlock.blockSpan]
  refine Submodule.mul_le_of_le_span_range
    (a := fun k => barL f (![] : Fin 0 → Fin 1 ⊕ Fin 3)
      ((Basis.conj LeptonDoubletV.basis).dualBasis k))
    (b := fun k : (Fin 1 ⊕ Fin 3) × (Fin 2 × Fin 2) =>
      L f' ![k.1] (LeptonDoubletV.basis.dualBasis k.2))
    (le_of_eq (LinearMap.range_eq_span_range_basis (Basis.conj LeptonDoubletV.basis).dualBasis _))
    (iSup_le fun μ => ?_) ?_
  · rw [LinearMap.range_eq_span_range_basis LeptonDoubletV.basis.dualBasis (L f' ![μ])]
    exact Submodule.span_mono (Set.range_subset_iff.2 fun k => ⟨(μ, k), rfl⟩)
  · intro i j
    exact Submodule.mem_iSup_of_mem (j.1, (j.2.1, i.1), (i.2, j.2.2))
      (Submodule.subset_span ⟨![0, 0], by
        simp only [barLLKineticBlock, barLLBlk, barLComponent, LComponent,
          Matrix.cons_val_zero, Matrix.cons_val_one, Prod.mk.eta]⟩)

/-- The `barL ∂ L` block reduces to its kinetic term. -/
lemma reducesInvariantsTo_barLL (f f' : Fin 3) :
    ReducesInvariantsTo (gaugeLorentzMaps repGauge repLorentz) (barLLPairSubmodule f f')
      (ℂ ∙ (barLLKineticBlock f f').kineticTerm) :=
  (barLLKineticBlock f f').reducesInvariantsTo.mono_left
    (barLLPairSubmodule_le_blockSpan f f')

/-- The submodule of the `e ∂ bare` block of a generation pair, an underived
  lepton-singlet range against the once-derived conjugate lepton-singlet ranges,
  joined over the derivative direction. -/
noncomputable def ebarePairSubmodule (f f' : Fin 3) :
    Submodule ℂ fieldData.LocalCovFieldAlgebra :=
  LinearMap.range (e f (![] : Fin 0 → Fin 1 ⊕ Fin 3))
    * ⨆ μ : Fin 1 ⊕ Fin 3, LinearMap.range (bare f' ![μ])

/-- The `e ∂ bare` block submodule is carried into itself by both groups. -/
lemma isStableUnder_ebarePairSubmodule (f f' : Fin 3) :
    IsStableUnder (gaugeLorentzMaps repGauge repLorentz) (ebarePairSubmodule f f') := by
  rw [ebarePairSubmodule]
  exact IsStableUnder.mul (gaugeLorentzMaps_mul repGauge_mul repLorentz_mul)
    (isStableUnder_range_underived (F := e f) (fun g φ => repGauge_e g f ![] φ)
      (repLorentz_e f))
    (isStableUnder_iSup_range_derived (F := bare f')
      (fun g μ φ => repGauge_bare g f' ![μ] φ) (repLorentz_bare f'))

/-- The `e ∂ bare` block submodule lies in the span of the block's components. -/
lemma ebarePairSubmodule_le_blockSpan (f f' : Fin 3) :
    ebarePairSubmodule f f' ≤ (ebareKineticBlock f f').blockSpan := by
  rw [ebarePairSubmodule, KineticBlock.blockSpan]
  refine Submodule.mul_le_of_le_span_range
    (a := fun k => e f (![] : Fin 0 → Fin 1 ⊕ Fin 3) (LeptonSinglet.basis.dualBasis k))
    (b := fun k : (Fin 1 ⊕ Fin 3) × (Fin 2) =>
      bare f' ![k.1] ((Basis.conj LeptonSinglet.basis).dualBasis k.2))
    (le_of_eq (LinearMap.range_eq_span_range_basis LeptonSinglet.basis.dualBasis _))
    (iSup_le fun μ => ?_) ?_
  · rw [LinearMap.range_eq_span_range_basis (Basis.conj LeptonSinglet.basis).dualBasis
    (bare f' ![μ])]
    exact Submodule.span_mono (Set.range_subset_iff.2 fun k => ⟨(μ, k), rfl⟩)
  · intro i j
    exact Submodule.mem_iSup_of_mem (j.1, (j.2, i), (0, 0))
      (Submodule.subset_span ⟨![0, 0], rfl⟩)

/-- The `e ∂ bare` block reduces to its kinetic term. -/
lemma reducesInvariantsTo_ebare (f f' : Fin 3) :
    ReducesInvariantsTo (gaugeLorentzMaps repGauge repLorentz) (ebarePairSubmodule f f')
      (ℂ ∙ (ebareKineticBlock f f').kineticTerm) :=
  (ebareKineticBlock f f').reducesInvariantsTo.mono_left
    (ebarePairSubmodule_le_blockSpan f f')

/-- The submodule of the `bare ∂ e` block of a generation pair, an underived
  conjugate lepton-singlet range against the once-derived lepton-singlet ranges,
  joined over the derivative direction. -/
noncomputable def bareePairSubmodule (f f' : Fin 3) :
    Submodule ℂ fieldData.LocalCovFieldAlgebra :=
  LinearMap.range (bare f (![] : Fin 0 → Fin 1 ⊕ Fin 3))
    * ⨆ μ : Fin 1 ⊕ Fin 3, LinearMap.range (e f' ![μ])

/-- The `bare ∂ e` block submodule is carried into itself by both groups. -/
lemma isStableUnder_bareePairSubmodule (f f' : Fin 3) :
    IsStableUnder (gaugeLorentzMaps repGauge repLorentz) (bareePairSubmodule f f') := by
  rw [bareePairSubmodule]
  exact IsStableUnder.mul (gaugeLorentzMaps_mul repGauge_mul repLorentz_mul)
    (isStableUnder_range_underived (F := bare f) (fun g φ => repGauge_bare g f ![] φ)
      (repLorentz_bare f))
    (isStableUnder_iSup_range_derived (F := e f')
      (fun g μ φ => repGauge_e g f' ![μ] φ) (repLorentz_e f'))

/-- The `bare ∂ e` block submodule lies in the span of the block's components. -/
lemma bareePairSubmodule_le_blockSpan (f f' : Fin 3) :
    bareePairSubmodule f f' ≤ (bareeKineticBlock f f').blockSpan := by
  rw [bareePairSubmodule, KineticBlock.blockSpan]
  refine Submodule.mul_le_of_le_span_range
    (a := fun k => bare f (![] : Fin 0 → Fin 1 ⊕ Fin 3)
      ((Basis.conj LeptonSinglet.basis).dualBasis k))
    (b := fun k : (Fin 1 ⊕ Fin 3) × (Fin 2) =>
      e f' ![k.1] (LeptonSinglet.basis.dualBasis k.2))
    (le_of_eq (LinearMap.range_eq_span_range_basis (Basis.conj LeptonSinglet.basis).dualBasis _))
    (iSup_le fun μ => ?_) ?_
  · rw [LinearMap.range_eq_span_range_basis LeptonSinglet.basis.dualBasis (e f' ![μ])]
    exact Submodule.span_mono (Set.range_subset_iff.2 fun k => ⟨(μ, k), rfl⟩)
  · intro i j
    exact Submodule.mem_iSup_of_mem (j.1, (i, j.2), (0, 0))
      (Submodule.subset_span ⟨![0, 0], rfl⟩)

/-- The `bare ∂ e` block reduces to its kinetic term. -/
lemma reducesInvariantsTo_baree (f f' : Fin 3) :
    ReducesInvariantsTo (gaugeLorentzMaps repGauge repLorentz) (bareePairSubmodule f f')
      (ℂ ∙ (bareeKineticBlock f f').kineticTerm) :=
  (bareeKineticBlock f f').reducesInvariantsTo.mono_left
    (bareePairSubmodule_le_blockSpan f f')

/-!

## C. The symbol ranges inside the derivative submodules, and the mass weight

An underived symbol range lies in `derivSubmodule 0` and a once-derived one in
`derivSubmodule 1`, so every component of a kinetic block is a product of the two, which
is `massWeightSubmodule 8`. Each stage of a block's classification stays inside the span
of the stage before it, so the kinetic term is there too.

-/

/-- The range of the down-singlet symbols lies in the derivative
  submodule of its slots. -/
lemma range_d_le_derivSubmodule {n : ℕ} (f : Fin 3) (l : Fin n → Fin 1 ⊕ Fin 3) :
    LinearMap.range (d f l) ≤ derivSubmodule n := by
  rw [derivSubmodule]
  refine le_iSup_of_le f (le_iSup_of_le l ?_)
  exact le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left
    (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left
    (le_sup_of_le_left (le_rfl)))))))))

/-- The range of the conjugate down-singlet symbols lies in the derivative
  submodule of its slots. -/
lemma range_bard_le_derivSubmodule {n : ℕ} (f : Fin 3) (l : Fin n → Fin 1 ⊕ Fin 3) :
    LinearMap.range (bard f l) ≤ derivSubmodule n := by
  rw [derivSubmodule]
  refine le_iSup_of_le f (le_iSup_of_le l ?_)
  exact le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left
    (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left
    (le_sup_of_le_right (le_rfl)))))))))

/-- The range of the up-singlet symbols lies in the derivative
  submodule of its slots. -/
lemma range_u_le_derivSubmodule {n : ℕ} (f : Fin 3) (l : Fin n → Fin 1 ⊕ Fin 3) :
    LinearMap.range (u f l) ≤ derivSubmodule n := by
  rw [derivSubmodule]
  refine le_iSup_of_le f (le_iSup_of_le l ?_)
  exact le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left
    (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_right
    (le_rfl))))))))

/-- The range of the conjugate up-singlet symbols lies in the derivative
  submodule of its slots. -/
lemma range_baru_le_derivSubmodule {n : ℕ} (f : Fin 3) (l : Fin n → Fin 1 ⊕ Fin 3) :
    LinearMap.range (baru f l) ≤ derivSubmodule n := by
  rw [derivSubmodule]
  refine le_iSup_of_le f (le_iSup_of_le l ?_)
  exact le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left
    (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_right (le_rfl)))))))

/-- The range of the quark-doublet symbols lies in the derivative
  submodule of its slots. -/
lemma range_Q_le_derivSubmodule {n : ℕ} (f : Fin 3) (l : Fin n → Fin 1 ⊕ Fin 3) :
    LinearMap.range (Q f l) ≤ derivSubmodule n := by
  rw [derivSubmodule]
  refine le_iSup_of_le f (le_iSup_of_le l ?_)
  exact le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left
    (le_sup_of_le_left (le_sup_of_le_right (le_rfl))))))

/-- The range of the conjugate quark-doublet symbols lies in the derivative
  submodule of its slots. -/
lemma range_barQ_le_derivSubmodule {n : ℕ} (f : Fin 3) (l : Fin n → Fin 1 ⊕ Fin 3) :
    LinearMap.range (barQ f l) ≤ derivSubmodule n := by
  rw [derivSubmodule]
  refine le_iSup_of_le f (le_iSup_of_le l ?_)
  exact le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left
    (le_sup_of_le_right (le_rfl)))))

/-- The range of the lepton-doublet symbols lies in the derivative
  submodule of its slots. -/
lemma range_L_le_derivSubmodule {n : ℕ} (f : Fin 3) (l : Fin n → Fin 1 ⊕ Fin 3) :
    LinearMap.range (L f l) ≤ derivSubmodule n := by
  rw [derivSubmodule]
  refine le_iSup_of_le f (le_iSup_of_le l ?_)
  exact le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_right (le_rfl))))

/-- The range of the conjugate lepton-doublet symbols lies in the derivative
  submodule of its slots. -/
lemma range_barL_le_derivSubmodule {n : ℕ} (f : Fin 3) (l : Fin n → Fin 1 ⊕ Fin 3) :
    LinearMap.range (barL f l) ≤ derivSubmodule n := by
  rw [derivSubmodule]
  refine le_iSup_of_le f (le_iSup_of_le l ?_)
  exact le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_right (le_rfl)))

/-- The range of the lepton-singlet symbols lies in the derivative
  submodule of its slots. -/
lemma range_e_le_derivSubmodule {n : ℕ} (f : Fin 3) (l : Fin n → Fin 1 ⊕ Fin 3) :
    LinearMap.range (e f l) ≤ derivSubmodule n := by
  rw [derivSubmodule]
  refine le_iSup_of_le f (le_iSup_of_le l ?_)
  exact le_sup_of_le_left (le_sup_of_le_right (le_rfl))

/-- The range of the conjugate lepton-singlet symbols lies in the derivative
  submodule of its slots. -/
lemma range_bare_le_derivSubmodule {n : ℕ} (f : Fin 3) (l : Fin n → Fin 1 ⊕ Fin 3) :
    LinearMap.range (bare f l) ≤ derivSubmodule n := by
  rw [derivSubmodule]
  refine le_iSup_of_le f (le_iSup_of_le l ?_)
  exact le_sup_of_le_right (le_rfl)

/-- The kinetic term of the `d ∂ bard` block has mass weight eight, since every component of the
  block is an underived tower against a once-derived one. -/
lemma dbardKineticTerm_mem_massWeightSubmodule (f f' : Fin 3) :
    (dbardKineticBlock f f').kineticTerm ∈ massWeightSubmodule 8 := by
  refine KineticBlock.kineticTerm_mem _ fun q l c c' w w' => ?_
  rw [massWeightSubmodule_eight_eq]
  exact Submodule.mul_mem_mul (range_d_le_derivSubmodule f ![] ⟨_, rfl⟩)
    (range_bard_le_derivSubmodule f' ![q] ⟨_, rfl⟩)

/-- The kinetic term of the `bard ∂ d` block has mass weight eight, since every component of the
  block is an underived tower against a once-derived one. -/
lemma barddKineticTerm_mem_massWeightSubmodule (f f' : Fin 3) :
    (barddKineticBlock f f').kineticTerm ∈ massWeightSubmodule 8 := by
  refine KineticBlock.kineticTerm_mem _ fun q l c c' w w' => ?_
  rw [massWeightSubmodule_eight_eq]
  exact Submodule.mul_mem_mul (range_bard_le_derivSubmodule f ![] ⟨_, rfl⟩)
    (range_d_le_derivSubmodule f' ![q] ⟨_, rfl⟩)

/-- The kinetic term of the `u ∂ baru` block has mass weight eight, since every component of the
  block is an underived tower against a once-derived one. -/
lemma ubaruKineticTerm_mem_massWeightSubmodule (f f' : Fin 3) :
    (ubaruKineticBlock f f').kineticTerm ∈ massWeightSubmodule 8 := by
  refine KineticBlock.kineticTerm_mem _ fun q l c c' w w' => ?_
  rw [massWeightSubmodule_eight_eq]
  exact Submodule.mul_mem_mul (range_u_le_derivSubmodule f ![] ⟨_, rfl⟩)
    (range_baru_le_derivSubmodule f' ![q] ⟨_, rfl⟩)

/-- The kinetic term of the `baru ∂ u` block has mass weight eight, since every component of the
  block is an underived tower against a once-derived one. -/
lemma baruuKineticTerm_mem_massWeightSubmodule (f f' : Fin 3) :
    (baruuKineticBlock f f').kineticTerm ∈ massWeightSubmodule 8 := by
  refine KineticBlock.kineticTerm_mem _ fun q l c c' w w' => ?_
  rw [massWeightSubmodule_eight_eq]
  exact Submodule.mul_mem_mul (range_baru_le_derivSubmodule f ![] ⟨_, rfl⟩)
    (range_u_le_derivSubmodule f' ![q] ⟨_, rfl⟩)

/-- The kinetic term of the `Q ∂ barQ` block has mass weight eight, since every component of the
  block is an underived tower against a once-derived one. -/
lemma QbarQKineticTerm_mem_massWeightSubmodule (f f' : Fin 3) :
    (QbarQKineticBlock f f').kineticTerm ∈ massWeightSubmodule 8 := by
  refine KineticBlock.kineticTerm_mem _ fun q l c c' w w' => ?_
  rw [massWeightSubmodule_eight_eq]
  exact Submodule.mul_mem_mul (range_Q_le_derivSubmodule f ![] ⟨_, rfl⟩)
    (range_barQ_le_derivSubmodule f' ![q] ⟨_, rfl⟩)

/-- The kinetic term of the `barQ ∂ Q` block has mass weight eight, since every component of the
  block is an underived tower against a once-derived one. -/
lemma barQQKineticTerm_mem_massWeightSubmodule (f f' : Fin 3) :
    (barQQKineticBlock f f').kineticTerm ∈ massWeightSubmodule 8 := by
  refine KineticBlock.kineticTerm_mem _ fun q l c c' w w' => ?_
  rw [massWeightSubmodule_eight_eq]
  exact Submodule.mul_mem_mul (range_barQ_le_derivSubmodule f ![] ⟨_, rfl⟩)
    (range_Q_le_derivSubmodule f' ![q] ⟨_, rfl⟩)

/-- The kinetic term of the `L ∂ barL` block has mass weight eight, since every component of the
  block is an underived tower against a once-derived one. -/
lemma LbarLKineticTerm_mem_massWeightSubmodule (f f' : Fin 3) :
    (LbarLKineticBlock f f').kineticTerm ∈ massWeightSubmodule 8 := by
  refine KineticBlock.kineticTerm_mem _ fun q l c c' w w' => ?_
  rw [massWeightSubmodule_eight_eq]
  exact Submodule.mul_mem_mul (range_L_le_derivSubmodule f ![] ⟨_, rfl⟩)
    (range_barL_le_derivSubmodule f' ![q] ⟨_, rfl⟩)

/-- The kinetic term of the `barL ∂ L` block has mass weight eight, since every component of the
  block is an underived tower against a once-derived one. -/
lemma barLLKineticTerm_mem_massWeightSubmodule (f f' : Fin 3) :
    (barLLKineticBlock f f').kineticTerm ∈ massWeightSubmodule 8 := by
  refine KineticBlock.kineticTerm_mem _ fun q l c c' w w' => ?_
  rw [massWeightSubmodule_eight_eq]
  exact Submodule.mul_mem_mul (range_barL_le_derivSubmodule f ![] ⟨_, rfl⟩)
    (range_L_le_derivSubmodule f' ![q] ⟨_, rfl⟩)

/-- The kinetic term of the `e ∂ bare` block has mass weight eight, since every component of the
  block is an underived tower against a once-derived one. -/
lemma ebareKineticTerm_mem_massWeightSubmodule (f f' : Fin 3) :
    (ebareKineticBlock f f').kineticTerm ∈ massWeightSubmodule 8 := by
  refine KineticBlock.kineticTerm_mem _ fun q l c c' w w' => ?_
  rw [massWeightSubmodule_eight_eq]
  exact Submodule.mul_mem_mul (range_e_le_derivSubmodule f ![] ⟨_, rfl⟩)
    (range_bare_le_derivSubmodule f' ![q] ⟨_, rfl⟩)

/-- The kinetic term of the `bare ∂ e` block has mass weight eight, since every component of the
  block is an underived tower against a once-derived one. -/
lemma bareeKineticTerm_mem_massWeightSubmodule (f f' : Fin 3) :
    (bareeKineticBlock f f').kineticTerm ∈ massWeightSubmodule 8 := by
  refine KineticBlock.kineticTerm_mem _ fun q l c c' w w' => ?_
  rw [massWeightSubmodule_eight_eq]
  exact Submodule.mul_mem_mul (range_bare_le_derivSubmodule f ![] ⟨_, rfl⟩)
    (range_e_le_derivSubmodule f' ![q] ⟨_, rfl⟩)

/-!

## D. The kinetic span

The kinetic span of the fermion sector at mass weight eight is the join, over the ten
conjugate pairings and the nine pairs of generations, of the lines through the kinetic
terms. Each generator is a gauge and Lorentz invariant of mass weight eight, which is the
easy direction of the classification and what makes it an equivalence rather than an
inclusion.

-/

/-- The kinetic span of the fermion sector at mass weight eight, the join of the ten
  conjugate pairings, each over the nine pairs of generations. -/
noncomputable def kineticSpan : Submodule ℂ fieldData.LocalCovFieldAlgebra :=
  ⨆ (f : Fin 3) (f' : Fin 3),
      ℂ ∙ (dbardKineticBlock f f').kineticTerm
        ⊔ ℂ ∙ (barddKineticBlock f f').kineticTerm
        ⊔ ℂ ∙ (ubaruKineticBlock f f').kineticTerm
        ⊔ ℂ ∙ (baruuKineticBlock f f').kineticTerm
        ⊔ ℂ ∙ (QbarQKineticBlock f f').kineticTerm
        ⊔ ℂ ∙ (barQQKineticBlock f f').kineticTerm
        ⊔ ℂ ∙ (LbarLKineticBlock f f').kineticTerm
        ⊔ ℂ ∙ (barLLKineticBlock f f').kineticTerm
        ⊔ ℂ ∙ (ebareKineticBlock f f').kineticTerm
        ⊔ ℂ ∙ (bareeKineticBlock f f').kineticTerm

/-- The line through the `dbard` kinetic term lies in the kinetic span. -/
lemma span_dbard_le_kineticSpan (f f' : Fin 3) :
    ℂ ∙ (dbardKineticBlock f f').kineticTerm ≤ kineticSpan := by
  rw [kineticSpan]
  refine le_iSup₂_of_le f f' ?_
  exact le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left
    (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left
    (le_sup_of_le_left (le_rfl)))))))))

/-- The line through the `bardd` kinetic term lies in the kinetic span. -/
lemma span_bardd_le_kineticSpan (f f' : Fin 3) :
    ℂ ∙ (barddKineticBlock f f').kineticTerm ≤ kineticSpan := by
  rw [kineticSpan]
  refine le_iSup₂_of_le f f' ?_
  exact le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left
    (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left
    (le_sup_of_le_right (le_rfl)))))))))

/-- The line through the `ubaru` kinetic term lies in the kinetic span. -/
lemma span_ubaru_le_kineticSpan (f f' : Fin 3) :
    ℂ ∙ (ubaruKineticBlock f f').kineticTerm ≤ kineticSpan := by
  rw [kineticSpan]
  refine le_iSup₂_of_le f f' ?_
  exact le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left
    (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_right (le_rfl))))))))

/-- The line through the `baruu` kinetic term lies in the kinetic span. -/
lemma span_baruu_le_kineticSpan (f f' : Fin 3) :
    ℂ ∙ (baruuKineticBlock f f').kineticTerm ≤ kineticSpan := by
  rw [kineticSpan]
  refine le_iSup₂_of_le f f' ?_
  exact le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left
    (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_right (le_rfl)))))))

/-- The line through the `QbarQ` kinetic term lies in the kinetic span. -/
lemma span_QbarQ_le_kineticSpan (f f' : Fin 3) :
    ℂ ∙ (QbarQKineticBlock f f').kineticTerm ≤ kineticSpan := by
  rw [kineticSpan]
  refine le_iSup₂_of_le f f' ?_
  exact le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left
    (le_sup_of_le_left (le_sup_of_le_right (le_rfl))))))

/-- The line through the `barQQ` kinetic term lies in the kinetic span. -/
lemma span_barQQ_le_kineticSpan (f f' : Fin 3) :
    ℂ ∙ (barQQKineticBlock f f').kineticTerm ≤ kineticSpan := by
  rw [kineticSpan]
  refine le_iSup₂_of_le f f' ?_
  exact le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left
    (le_sup_of_le_right (le_rfl)))))

/-- The line through the `LbarL` kinetic term lies in the kinetic span. -/
lemma span_LbarL_le_kineticSpan (f f' : Fin 3) :
    ℂ ∙ (LbarLKineticBlock f f').kineticTerm ≤ kineticSpan := by
  rw [kineticSpan]
  refine le_iSup₂_of_le f f' ?_
  exact le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_right (le_rfl))))

/-- The line through the `barLL` kinetic term lies in the kinetic span. -/
lemma span_barLL_le_kineticSpan (f f' : Fin 3) :
    ℂ ∙ (barLLKineticBlock f f').kineticTerm ≤ kineticSpan := by
  rw [kineticSpan]
  refine le_iSup₂_of_le f f' ?_
  exact le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_right (le_rfl)))

/-- The line through the `ebare` kinetic term lies in the kinetic span. -/
lemma span_ebare_le_kineticSpan (f f' : Fin 3) :
    ℂ ∙ (ebareKineticBlock f f').kineticTerm ≤ kineticSpan := by
  rw [kineticSpan]
  refine le_iSup₂_of_le f f' ?_
  exact le_sup_of_le_left (le_sup_of_le_right (le_rfl))

/-- The line through the `baree` kinetic term lies in the kinetic span. -/
lemma span_baree_le_kineticSpan (f f' : Fin 3) :
    ℂ ∙ (bareeKineticBlock f f').kineticTerm ≤ kineticSpan := by
  rw [kineticSpan]
  refine le_iSup₂_of_le f f' ?_
  exact le_sup_of_le_right (le_rfl)

/-- The kinetic span is fixed pointwise by both groups, each of its generators being a
  gauge and Lorentz invariant. -/
lemma isFixedBy_kineticSpan :
    IsFixedBy (gaugeLorentzMaps repGauge repLorentz) kineticSpan := by
  rw [kineticSpan]
  refine isFixedBy_iSup fun f => isFixedBy_iSup fun f' => ?_
  exact IsFixedBy.sup
    (IsFixedBy.sup
    (IsFixedBy.sup
    (IsFixedBy.sup
    (IsFixedBy.sup
    (IsFixedBy.sup
    (IsFixedBy.sup
    (IsFixedBy.sup
    (IsFixedBy.sup
    (isFixedBy_span_singleton (forall_gaugeLorentzMaps_eq_self_iff.2
      ⟨(dbardKineticBlock f f').repGauge_kineticTerm,
        (dbardKineticBlock f f').repLorentz_kineticTerm⟩))
    (isFixedBy_span_singleton (forall_gaugeLorentzMaps_eq_self_iff.2
      ⟨(barddKineticBlock f f').repGauge_kineticTerm,
        (barddKineticBlock f f').repLorentz_kineticTerm⟩)))
    (isFixedBy_span_singleton (forall_gaugeLorentzMaps_eq_self_iff.2
      ⟨(ubaruKineticBlock f f').repGauge_kineticTerm,
        (ubaruKineticBlock f f').repLorentz_kineticTerm⟩)))
    (isFixedBy_span_singleton (forall_gaugeLorentzMaps_eq_self_iff.2
      ⟨(baruuKineticBlock f f').repGauge_kineticTerm,
        (baruuKineticBlock f f').repLorentz_kineticTerm⟩)))
    (isFixedBy_span_singleton (forall_gaugeLorentzMaps_eq_self_iff.2
      ⟨(QbarQKineticBlock f f').repGauge_kineticTerm,
        (QbarQKineticBlock f f').repLorentz_kineticTerm⟩)))
    (isFixedBy_span_singleton (forall_gaugeLorentzMaps_eq_self_iff.2
      ⟨(barQQKineticBlock f f').repGauge_kineticTerm,
        (barQQKineticBlock f f').repLorentz_kineticTerm⟩)))
    (isFixedBy_span_singleton (forall_gaugeLorentzMaps_eq_self_iff.2
      ⟨(LbarLKineticBlock f f').repGauge_kineticTerm,
        (LbarLKineticBlock f f').repLorentz_kineticTerm⟩)))
    (isFixedBy_span_singleton (forall_gaugeLorentzMaps_eq_self_iff.2
      ⟨(barLLKineticBlock f f').repGauge_kineticTerm,
        (barLLKineticBlock f f').repLorentz_kineticTerm⟩)))
    (isFixedBy_span_singleton (forall_gaugeLorentzMaps_eq_self_iff.2
      ⟨(ebareKineticBlock f f').repGauge_kineticTerm,
        (ebareKineticBlock f f').repLorentz_kineticTerm⟩)))
    (isFixedBy_span_singleton (forall_gaugeLorentzMaps_eq_self_iff.2
      ⟨(bareeKineticBlock f f').repGauge_kineticTerm,
        (bareeKineticBlock f f').repLorentz_kineticTerm⟩))

/-- The kinetic span lies at mass weight eight. -/
lemma kineticSpan_le_massWeightSubmodule : kineticSpan ≤ massWeightSubmodule 8 := by
  rw [kineticSpan]
  refine iSup_le fun f => iSup_le fun f' => ?_
  refine sup_le (sup_le (sup_le (sup_le (sup_le (sup_le (sup_le (sup_le (sup_le
    ?_ ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_
  · exact (Submodule.span_singleton_le_iff_mem _ _).2
      (dbardKineticTerm_mem_massWeightSubmodule f f')
  · exact (Submodule.span_singleton_le_iff_mem _ _).2
      (barddKineticTerm_mem_massWeightSubmodule f f')
  · exact (Submodule.span_singleton_le_iff_mem _ _).2
      (ubaruKineticTerm_mem_massWeightSubmodule f f')
  · exact (Submodule.span_singleton_le_iff_mem _ _).2
      (baruuKineticTerm_mem_massWeightSubmodule f f')
  · exact (Submodule.span_singleton_le_iff_mem _ _).2
      (QbarQKineticTerm_mem_massWeightSubmodule f f')
  · exact (Submodule.span_singleton_le_iff_mem _ _).2
      (barQQKineticTerm_mem_massWeightSubmodule f f')
  · exact (Submodule.span_singleton_le_iff_mem _ _).2
      (LbarLKineticTerm_mem_massWeightSubmodule f f')
  · exact (Submodule.span_singleton_le_iff_mem _ _).2
      (barLLKineticTerm_mem_massWeightSubmodule f f')
  · exact (Submodule.span_singleton_le_iff_mem _ _).2
      (ebareKineticTerm_mem_massWeightSubmodule f f')
  · exact (Submodule.span_singleton_le_iff_mem _ _).2
      (bareeKineticTerm_mem_massWeightSubmodule f f')

/-!

## E. The blocks reduce to the kinetic terms

The weight-zero piece of the gauge weight decomposition lies in the join of the ten block
submodules, hypercharge having already cut the hundred pairings down to ten; and each
block reduces to its kinetic term, by the three stages its `KineticBlock` package supplies.
Joining the ten and then the nine generation pairs is `ReducesInvariantsTo.sup` and
`ReducesInvariantsTo.iSup`, which is where the stability of the blocks and of the kinetic span is
spent.

-/

/-- The ten block submodules of a generation pair, joined. -/
noncomputable def kineticPairSubmodule (f f' : Fin 3) :
    Submodule ℂ fieldData.LocalCovFieldAlgebra :=
  dbardPairSubmodule f f'
    ⊔ barddPairSubmodule f f'
    ⊔ ubaruPairSubmodule f f'
    ⊔ baruuPairSubmodule f f'
    ⊔ QbarQPairSubmodule f f'
    ⊔ barQQPairSubmodule f f'
    ⊔ LbarLPairSubmodule f f'
    ⊔ barLLPairSubmodule f f'
    ⊔ ebarePairSubmodule f f'
    ⊔ bareePairSubmodule f f'

/-- The join of the ten block submodules over the nine pairs of generations. -/
noncomputable def kineticBlockSubmodule :
    Submodule ℂ fieldData.LocalCovFieldAlgebra :=
  ⨆ (f : Fin 3) (f' : Fin 3), kineticPairSubmodule f f'

/-- The joined block submodules of a generation pair are carried into themselves by both
  groups, each block submodule being. -/
lemma isStableUnder_kineticPairSubmodule (f f' : Fin 3) :
    IsStableUnder (gaugeLorentzMaps repGauge repLorentz) (kineticPairSubmodule f f') :=
  IsStableUnder.sup
    (IsStableUnder.sup
    (IsStableUnder.sup
    (IsStableUnder.sup
    (IsStableUnder.sup
    (IsStableUnder.sup
    (IsStableUnder.sup
    (IsStableUnder.sup
    (IsStableUnder.sup
    (isStableUnder_dbardPairSubmodule f f')
    (isStableUnder_barddPairSubmodule f f'))
    (isStableUnder_ubaruPairSubmodule f f'))
    (isStableUnder_baruuPairSubmodule f f'))
    (isStableUnder_QbarQPairSubmodule f f'))
    (isStableUnder_barQQPairSubmodule f f'))
    (isStableUnder_LbarLPairSubmodule f f'))
    (isStableUnder_barLLPairSubmodule f f'))
    (isStableUnder_ebarePairSubmodule f f'))
    (isStableUnder_bareePairSubmodule f f')

/-- The joined block submodules of a generation pair reduce to the kinetic span, each block
  reducing to its kinetic term. -/
lemma reducesInvariantsTo_kineticPairSubmodule (f f' : Fin 3) :
    ReducesInvariantsTo (gaugeLorentzMaps repGauge repLorentz) (kineticPairSubmodule f f')
      kineticSpan := by
  have hW : IsStableUnder (gaugeLorentzMaps repGauge repLorentz) kineticSpan :=
    isFixedBy_kineticSpan.isStableUnder
  exact ReducesInvariantsTo.sup
    (ReducesInvariantsTo.sup
    (ReducesInvariantsTo.sup
    (ReducesInvariantsTo.sup
    (ReducesInvariantsTo.sup
    (ReducesInvariantsTo.sup
    (ReducesInvariantsTo.sup
    (ReducesInvariantsTo.sup
    (ReducesInvariantsTo.sup
    ((reducesInvariantsTo_dbard f f').mono_right (span_dbard_le_kineticSpan f f'))
    ((reducesInvariantsTo_bardd f f').mono_right (span_bardd_le_kineticSpan f f'))
    (isStableUnder_barddPairSubmodule f f') hW)
    ((reducesInvariantsTo_ubaru f f').mono_right (span_ubaru_le_kineticSpan f f'))
    (isStableUnder_ubaruPairSubmodule f f') hW)
    ((reducesInvariantsTo_baruu f f').mono_right (span_baruu_le_kineticSpan f f'))
    (isStableUnder_baruuPairSubmodule f f') hW)
    ((reducesInvariantsTo_QbarQ f f').mono_right (span_QbarQ_le_kineticSpan f f'))
    (isStableUnder_QbarQPairSubmodule f f') hW)
    ((reducesInvariantsTo_barQQ f f').mono_right (span_barQQ_le_kineticSpan f f'))
    (isStableUnder_barQQPairSubmodule f f') hW)
    ((reducesInvariantsTo_LbarL f f').mono_right (span_LbarL_le_kineticSpan f f'))
    (isStableUnder_LbarLPairSubmodule f f') hW)
    ((reducesInvariantsTo_barLL f f').mono_right (span_barLL_le_kineticSpan f f'))
    (isStableUnder_barLLPairSubmodule f f') hW)
    ((reducesInvariantsTo_ebare f f').mono_right (span_ebare_le_kineticSpan f f'))
    (isStableUnder_ebarePairSubmodule f f') hW)
    ((reducesInvariantsTo_baree f f').mono_right (span_baree_le_kineticSpan f f'))
    (isStableUnder_bareePairSubmodule f f') hW

/-- The weight-zero piece at mass weight eight lies in the join of the ten block submodules, since
  each of the ten conjugate pairings of `massWeightSubmoduleGaugeWeightEight_piece_zero` is an
  underived range against a once-derived one, and the derivative direction is joined over. -/
lemma massWeightSubmoduleGaugeWeightEight_piece_zero_le :
    (massWeightSubmoduleGaugeWeightEight).piece 0 ≤ kineticBlockSubmodule := by
  rw [massWeightSubmoduleGaugeWeightEight_piece_zero, kineticBlockSubmodule]
  refine iSup_le fun f => iSup_le fun f' => iSup_le fun l' => ?_
  obtain ⟨μ, rfl⟩ : ∃ μ, l' = ![μ] := ⟨l' 0, (vecCons_fin_one_eta l').symm⟩
  refine le_iSup₂_of_le f f' ?_
  simp only [kineticPairSubmodule, dbardPairSubmodule, barddPairSubmodule, ubaruPairSubmodule,
    baruuPairSubmodule, QbarQPairSubmodule, barQQPairSubmodule, LbarLPairSubmodule,
    barLLPairSubmodule, ebarePairSubmodule, bareePairSubmodule]
  refine sup_le_sup (sup_le_sup (sup_le_sup (sup_le_sup (sup_le_sup (sup_le_sup (sup_le_sup
    (sup_le_sup (sup_le_sup ?_ ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_ <;>
  exact (GaugeWeightDecomposition.piece_le_self _ 0).trans
    (mul_le_mul' le_rfl (le_iSup_of_le μ le_rfl))

/-- The join of the ten block submodules reduces to the kinetic span. -/
lemma reducesInvariantsTo_kineticBlockSubmodule :
    ReducesInvariantsTo (gaugeLorentzMaps repGauge repLorentz) kineticBlockSubmodule
      kineticSpan := by
  have hW : IsStableUnder (gaugeLorentzMaps repGauge repLorentz) kineticSpan :=
    isFixedBy_kineticSpan.isStableUnder
  rw [kineticBlockSubmodule]
  exact ReducesInvariantsTo.iSup (fun f => ReducesInvariantsTo.iSup
      (reducesInvariantsTo_kineticPairSubmodule f) (isStableUnder_kineticPairSubmodule f) hW)
    (fun f => isStableUnder_iSup fun f' => isStableUnder_kineticPairSubmodule f f') hW

/-!

## F. The classification as an equivalence

The two directions meet. Forwards, hypercharge puts a gauge invariant in the weight-zero
piece (`GaugeWeightDecomposition.reducesInvariantsTo_piece_zero`), and section E reduces
that to the kinetic span. Backwards, the kinetic span is a space of gauge and Lorentz
invariants of mass weight eight (section D), which turns the reduction into an equivalence.

So the fermion sector at mass weight eight carries exactly the kinetic terms — one for
each species, each pair of generations and each placement of the derivative — and nothing
else. Compare mass weight six, where the same argument leaves nothing at all. Without a
derivative there is no four-vector index for the conjugate Pauli matrices to carry, and
the Dirac mass term does not exist.

-/

/-- The fermion sector at mass weight eight reduces, for the gauge and Lorentz groups
  together, to the kinetic span. The torus puts an invariant in the weight-zero piece, which
  lies in the ten block submodules, and those reduce to the kinetic terms. -/
lemma reducesInvariantsTo_kineticSpan :
    ReducesInvariantsTo (gaugeLorentzMaps repGauge repLorentz) (massWeightSubmodule 8)
      kineticSpan :=
  (ReducesInvariantsTo.ofGauge (ReducesInvariantsTo.comp (σ := fun g : GaugeGroupI => repGauge g)
    gaugeTorusGen massWeightSubmoduleGaugeWeightEight.reducesInvariantsTo_piece_zero)).trans
    (reducesInvariantsTo_kineticBlockSubmodule.mono_left
      massWeightSubmoduleGaugeWeightEight_piece_zero_le)

/-- The classification of mass weight eight as an equivalence, in the shape of the
  sibling sectors. An element of `massWeightSubmodule 8 ⊔ S` is fixed by both groups
  exactly when it is a combination of the kinetic terms up to a remainder in `S` fixed by
  both groups. -/
lemma mem_massWeightSubmodule_eight_sup_and_gauge_lorentz_invariant_iff
    (S : Submodule ℂ fieldData.LocalCovFieldAlgebra)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, repGauge g y ∈ S)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) (x : fieldData.LocalCovFieldAlgebra) :
    (x ∈ massWeightSubmodule 8 ⊔ S ∧ (∀ g : GaugeGroupI, repGauge g x = x)
        ∧ ∀ g : SL(2,ℂ), repLorentz g x = x)
      ↔ ∃ y ∈ S, (∀ g : GaugeGroupI, repGauge g y = y)
          ∧ (∀ g : SL(2,ℂ), repLorentz g y = y)
          ∧ x - y ∈ kineticSpan :=
  ReducesInvariantsTo.mem_sup_and_gauge_lorentz_invariant_iff reducesInvariantsTo_kineticSpan
    kineticSpan_le_massWeightSubmodule isFixedBy_kineticSpan hS hSL x

end FermionSector

end StandardModel
