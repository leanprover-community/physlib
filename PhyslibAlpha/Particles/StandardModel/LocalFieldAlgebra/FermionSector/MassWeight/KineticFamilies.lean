/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.Particles.StandardModel.LocalFieldAlgebra.FermionSector.MassWeight.MassDimLTEight
public import PhyslibAlpha.Particles.StandardModel.GaugeGroup.Invariants.Basic
public import PhyslibAlpha.Relativity.Tensors.ComplexTensor.Vector.InvariantCoeff
/-!
# The kinetic terms of the fermion sector

The package that turns a kinetic block of the fermion sector into its kinetic term and the
reduction of the block to it.

## i. Overview

The invariants of the fermion sector at mass weight eight are the kinetic terms, and this
file builds them. A kinetic term pairs a species with its own conjugate, one of the two
carrying a covariant derivative, and joins their indices in the only ways available. The
colour indices by the Kronecker delta, the isospin indices by the Kronecker delta, and the
four-vector index against the two opposite-chirality spinor indices by the conjugate Pauli
matrices. That last contraction is `ψ̄ σ̄^μ ∂_μ ψ`.

Ten blocks arise, the five conjugate pairs each with the derivative on one factor or the
other, and they differ only in which indices their symbols carry. So the work is done once,
generically, in terms of `InvariantReductionToSpan`: a `KineticBlock` packages a
block together with its three classification steps — colour, isospin, Lorentz — and from
that package alone come the contraction, its invariance under both groups, and the reduction
of the block down to the line through it. The ten blocks are then ten instantiations.

The three stages are the same three the Yukawa sector runs, in the same order, and for the
same reason: each contraction is a spectator of the ones after it. Where a block's symbols
carry no colour index — the two lepton-doublet blocks and the two lepton-singlet ones — the
colour stage is `InvariantReductionToSpan.ofFixedFamily` rather than a classification, and
likewise for isospin where the symbols carry none. That keeps all ten blocks in one shape.

The ten blocks themselves are built in `KineticTerms`, which instantiates the package.

## ii. Key results

- `KineticBlock` : one kinetic block of the fermion sector, together with the three classifications
  its indices admit.
- `KineticBlock.reducesInvariantsTo` : the block span reduces to the span of its kinetic term.
- `KineticBlock.repGauge_kineticTerm`, `KineticBlock.repLorentz_kineticTerm` : the kinetic term
  is gauge and Lorentz invariant.

## iii. Table of contents

- A. The once-derived chiral component families
- B. Products of two components
- C. The kinetic block package

## iv. References

* None.

-/

@[expose] public section

open TensorSpecies
open suTensor (fundAntiFundIdx)

namespace StandardModel

open Matrix MatrixGroups Lorentz ComplexConjugate

namespace FermionSector

/-!

## A. The once-derived chiral component families

A tower with one covariant derivative mixes into every assignment of one derivative
direction, so its Lorentz law is a sum over such assignments, with one column of the
Lorentz matrix per slot. The value index is untouched by that sum. It still moves by the
contragredient action, exactly as at zero derivatives. Composing the two gives the laws
`repLorentz_leftComp_deriv_one` and `repLorentz_rightComp_deriv_one`, the derivative slot
fundamental and the spinor slot dual.

-/

/-- The Lorentz transformation of a symbol with one covariant derivative. The derivative
  slot moves by the columns of the Lorentz matrix and the value index by the
  contragredient action. -/
lemma repLorentz_symbol_deriv_one {V : Type} [AddCommGroup V] [Module ℂ V]
    {rep : Representation ℂ SL(2,ℂ) V}
    {X : {n : ℕ} → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ V →ₗ[ℂ] fieldData.LocalCovFieldAlgebra}
    (hX : IsLorentzCovDerivTransforms repLorentz rep X) (Λ : SL(2,ℂ))
    (μ : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ V) :
    repLorentz Λ (X ![μ] φ)
      = ∑ ν, (((SL2C.toLorentzGroup Λ).1 ν μ : ℝ) : ℂ) • X ![ν] (rep.dual Λ φ) := by
  rw [hX Λ 1 ![μ] φ, sum_pi_fin_one]
  refine Finset.sum_congr rfl fun ν _ => ?_
  congr 1
  simp

/-- The Lorentz transformation of a component of a once-derived symbol, when the
  coordinate functionals `c` are permuted by the contragredient action with coefficients
  `m`. This is the once-derived form of the laws of `Components`. -/
lemma repLorentz_component_deriv_one {V : Type} [AddCommGroup V] [Module ℂ V]
    {rep : Representation ℂ SL(2,ℂ) V}
    {X : {n : ℕ} → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ V →ₗ[ℂ] fieldData.LocalCovFieldAlgebra}
    (hX : IsLorentzCovDerivTransforms repLorentz rep X)
    {c : Fin 2 → Module.Dual ℂ V} {m : SL(2,ℂ) → Fin 2 → Fin 2 → ℂ}
    (hc : ∀ (Λ : SL(2,ℂ)) (a : Fin 2), rep.dual Λ (c a) = ∑ β, m Λ a β • c β)
    (Λ : SL(2,ℂ)) (μ : Fin 1 ⊕ Fin 3) (a : Fin 2) :
    repLorentz Λ (X ![μ] (c a))
      = ∑ ν, ∑ β, ((((SL2C.toLorentzGroup Λ).1 ν μ : ℝ) : ℂ) * m Λ a β) • X ![ν] (c β) := by
  rw [repLorentz_symbol_deriv_one hX Λ μ (c a), hc]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [map_sum, Finset.smul_sum]
  exact Finset.sum_congr rfl fun β _ => by rw [map_smul, smul_smul]

/-- Every undotted component family carries a four-vector index and a dual undotted
  spinor index, at one covariant derivative. -/
lemma repLorentz_leftComp_deriv_one (i : LeftIdx) :
    ∀ (Λ : SL(2,ℂ)) (μ : Fin 1 ⊕ Fin 3) (a : Fin 2), repLorentz Λ (leftComp ![μ] i a)
      = ∑ ν, ∑ β, ((((SL2C.toLorentzGroup Λ).1 ν μ : ℝ) : ℂ) * (Λ⁻¹).1 a β) •
        leftComp ![ν] i β := by
  cases i with
  | bard f c =>
    exact fun Λ μ a => repLorentz_component_deriv_one (repLorentz_bard f)
      (fun Λ a => DownSinglet.repLorentzGroup_conj_dual_dualBasis Λ (a, c)) Λ μ a
  | baru f c =>
    exact fun Λ μ a => repLorentz_component_deriv_one (repLorentz_baru f)
      (fun Λ a => UpSinglet.repLorentzGroup_conj_dual_dualBasis Λ (a, c)) Λ μ a
  | Q f c s =>
    exact fun Λ μ a => repLorentz_component_deriv_one (repLorentz_Q f)
      (fun Λ a => QuarkDoublet.repLorentzGroup_dual_dualBasis Λ (a, c, s)) Λ μ a
  | L f s =>
    exact fun Λ μ a => repLorentz_component_deriv_one (repLorentz_L f)
      (fun Λ a => LeptonDoubletV.repLorentzGroup_dual_dualBasis Λ (a, s)) Λ μ a
  | bare f =>
    exact fun Λ μ a => repLorentz_component_deriv_one (repLorentz_bare f)
      (fun Λ a => LeptonSinglet.repLorentzGroup_conj_dual_dualBasis Λ a) Λ μ a

/-- Every dotted component family carries a four-vector index and a dual dotted spinor
  index, at one covariant derivative. -/
lemma repLorentz_rightComp_deriv_one (i : RightIdx) :
    ∀ (Λ : SL(2,ℂ)) (μ : Fin 1 ⊕ Fin 3) (a : Fin 2), repLorentz Λ (rightComp ![μ] i a)
      = ∑ ν, ∑ β, ((((SL2C.toLorentzGroup Λ).1 ν μ : ℝ) : ℂ) * star ((Λ⁻¹).1 a β)) •
        rightComp ![ν] i β := by
  cases i with
  | d f c =>
    exact fun Λ μ a => repLorentz_component_deriv_one (repLorentz_d f)
      (fun Λ a => DownSinglet.repLorentzGroup_dual_dualBasis Λ (a, c)) Λ μ a
  | u f c =>
    exact fun Λ μ a => repLorentz_component_deriv_one (repLorentz_u f)
      (fun Λ a => UpSinglet.repLorentzGroup_dual_dualBasis Λ (a, c)) Λ μ a
  | barQ f c s =>
    exact fun Λ μ a => repLorentz_component_deriv_one (repLorentz_barQ f)
      (fun Λ a => QuarkDoublet.repLorentzGroup_conj_dual_dualBasis Λ (a, c, s)) Λ μ a
  | barL f s =>
    exact fun Λ μ a => repLorentz_component_deriv_one (repLorentz_barL f)
      (fun Λ a => LeptonDoubletV.repLorentzGroup_conj_dual_dualBasis Λ (a, s)) Λ μ a
  | e f =>
    exact fun Λ μ a => repLorentz_component_deriv_one (repLorentz_e f)
      (fun Λ a => LeptonSinglet.repLorentzGroup_dual_dualBasis Λ a) Λ μ a

/-!

## B. Products of two components

A block is a product of two components, and each of its index laws comes from the laws of
the two factors. The representation respects multiplication, so the two transform
independently and their coefficients multiply. Which slot of the classifier a factor
occupies is decided by its variance, the fundamental one going first, so each law comes in
two arrangements according to which factor is the barred one.

-/

/-- A product of a component with a fundamental colour index and one with an
  anti-fundamental colour index carries one colour index of each kind. -/
lemma isEquivariant_colourFundAntiFund_mul
    {A C : Fin 3 → fieldData.LocalCovFieldAlgebra}
    (hA : ∀ (U : specialUnitaryGroup (Fin 3) ℂ) (c : Fin 3),
      repGauge ((U, 1, 1) : GaugeGroupI) (A c) = ∑ a, U.1 a c • A a)
    (hC : ∀ (U : specialUnitaryGroup (Fin 3) ℂ) (c : Fin 3),
      repGauge ((U, 1, 1) : GaugeGroupI) (C c) = ∑ a, conj (U.1 a c) • C a) :
    (suTensor 3).IsEquivariant ![.fund, .antiFund] (repGauge.comp GaugeGroupI.ofSU3)
      (liftComponents ((fun l : Fin 2 → Fin 3 => A (l 0) * C (l 1)) ∘ fundAntiFundIdx)) :=
  ColourFundAntiFund.of_law fun U l => by
    rw [repGauge_mul, hA, hC, Finset.sum_mul_sum, Physlib.Fin.sum_fin_two_arrow]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
      smul_mul_smul_comm _ _ _ _

/-- The same with the two factors exchanged, the anti-fundamental one first. -/
lemma isEquivariant_colourFundAntiFund_mul_swap
    {A C : Fin 3 → fieldData.LocalCovFieldAlgebra}
    (hA : ∀ (U : specialUnitaryGroup (Fin 3) ℂ) (c : Fin 3),
      repGauge ((U, 1, 1) : GaugeGroupI) (A c) = ∑ a, conj (U.1 a c) • A a)
    (hC : ∀ (U : specialUnitaryGroup (Fin 3) ℂ) (c : Fin 3),
      repGauge ((U, 1, 1) : GaugeGroupI) (C c) = ∑ a, U.1 a c • C a) :
    (suTensor 3).IsEquivariant ![.fund, .antiFund] (repGauge.comp GaugeGroupI.ofSU3)
      (liftComponents ((fun l : Fin 2 → Fin 3 => A (l 1) * C (l 0)) ∘ fundAntiFundIdx)) :=
  ColourFundAntiFund.of_law fun U l => by
    rw [repGauge_mul, hA, hC, Finset.sum_mul_sum, Physlib.Fin.sum_fin_two_arrow, Finset.sum_comm]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    rw [smul_mul_smul_comm, mul_comm]

/-- A product of a component with a fundamental isospin index and one with an
  anti-fundamental isospin index carries one isospin index of each kind. -/
lemma isEquivariant_isospinFundAntiFund_mul
    {A C : Fin 2 → fieldData.LocalCovFieldAlgebra}
    (hA : ∀ (V : specialUnitaryGroup (Fin 2) ℂ) (w : Fin 2),
      repGauge ((1, V, 1) : GaugeGroupI) (A w) = ∑ a, V.1 a w • A a)
    (hC : ∀ (V : specialUnitaryGroup (Fin 2) ℂ) (w : Fin 2),
      repGauge ((1, V, 1) : GaugeGroupI) (C w) = ∑ a, conj (V.1 a w) • C a) :
    (suTensor 2).IsEquivariant ![.fund, .antiFund] (repGauge.comp GaugeGroupI.ofSU2)
      (liftComponents ((fun l : Fin 2 → Fin 2 => A (l 0) * C (l 1)) ∘ fundAntiFundIdx)) :=
  IsospinFundAntiFund.of_law fun V l => by
    rw [repGauge_mul, hA, hC, Finset.sum_mul_sum, Physlib.Fin.sum_fin_two_arrow]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
      smul_mul_smul_comm _ _ _ _

/-- The same with the two factors exchanged, the anti-fundamental one first. -/
lemma isEquivariant_isospinFundAntiFund_mul_swap
    {A C : Fin 2 → fieldData.LocalCovFieldAlgebra}
    (hA : ∀ (V : specialUnitaryGroup (Fin 2) ℂ) (w : Fin 2),
      repGauge ((1, V, 1) : GaugeGroupI) (A w) = ∑ a, conj (V.1 a w) • A a)
    (hC : ∀ (V : specialUnitaryGroup (Fin 2) ℂ) (w : Fin 2),
      repGauge ((1, V, 1) : GaugeGroupI) (C w) = ∑ a, V.1 a w • C a) :
    (suTensor 2).IsEquivariant ![.fund, .antiFund] (repGauge.comp GaugeGroupI.ofSU2)
      (liftComponents ((fun l : Fin 2 → Fin 2 => A (l 1) * C (l 0)) ∘ fundAntiFundIdx)) :=
  IsospinFundAntiFund.of_law fun V l => by
    rw [repGauge_mul, hA, hC, Finset.sum_mul_sum, Physlib.Fin.sum_fin_two_arrow, Finset.sum_comm]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    rw [smul_mul_smul_comm, mul_comm]

/-- A product of two components that a gauge transformation fixes is fixed by it. This is the form
  in which a block whose symbols carry no colour, or no isospin, supplies the corresponding
  stage. -/
lemma repGauge_mul_fixed
    {g : GaugeGroupI} {a c : fieldData.LocalCovFieldAlgebra} (ha : repGauge g a = a)
    (hc : repGauge g c = c) :
    repGauge g (a * c) = a * c := by
  rw [repGauge_mul, ha, hc]

/-- A product of two components that a gauge transformation scales by reciprocal scalars
  is fixed by it. This is the form in which the hypercharges of a species and its conjugate
  cancel. -/
lemma repGauge_mul_smul_fixed
    {g : GaugeGroupI} {z z' : ℂ} {a c : fieldData.LocalCovFieldAlgebra} (hz : z * z' = 1)
    (ha : repGauge g a = z • a) (hc : repGauge g c = z' • c) :
    repGauge g (a * c) = a * c := by
  rw [repGauge_mul, ha, hc, smul_mul_smul_comm, hz, one_smul]



/-- A finite sum of families carrying one four-vector index and a pair of dual
  opposite-chirality Weyl indices is such a family again, the colour and isospin
  contractions are Lorentz spectators. -/
lemma isEquivariant_upDownRDownL_sum {ι : Type} [Fintype ι]
    {T : ι → (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2 → fieldData.LocalCovFieldAlgebra}
    (hT : ∀ i, complexLorentzTensor.IsEquivariant ![.up, .downR, .downL] repLorentz
      (liftComponents (T i ∘ dualIndexEquiv))) :
    complexLorentzTensor.IsEquivariant ![.up, .downR, .downL] repLorentz
      (liftComponents ((fun p => ∑ i, T i p) ∘ dualIndexEquiv)) :=
  TensorSpecies.isEquivariant_liftComponents_sum _ fun i _ => hT i


/-!

## C. The kinetic block package

A kinetic block is classified in three stages, and every block runs the same three: colour,
then isospin, then Lorentz, each contraction a spectator of the ones after it. `KineticBlock`
packages a block together with the three steps, and from the package alone come the kinetic
term, its invariance under both groups, and the reduction of the block to the line
through it.

The colour and isospin indices of the block are listed in the order the classifiers read
them, fundamental first; a block whose symbols carry no colour, or no isospin, simply
ignores the corresponding pair and supplies `InvariantReductionToSpan.ofFixedFamily` for that
stage. Each step comes with the fact that its contraction lies in the submodule it classifies, which
is what carries the invariance of one stage through the stages after it.

-/

section Blocks

variable {B : Type} [Ring B] [Algebra ℂ B]
  (repGauge : Representation ℂ GaugeGroupI B) (repLorentz : Representation ℂ SL(2,ℂ) B)

/-- One kinetic block of the fermion sector, together with the three classifications its
  indices admit. The block is indexed by the derivative direction, the pair of spinor
  indices in the order `(undotted, dotted)`, the pair of colour indices and the pair of
  isospin indices, each pair in the order `(fundamental, anti-fundamental)`. -/
structure KineticBlock where
  /-- The components of the block. -/
  blk : (Fin 1 ⊕ Fin 3) → Fin 2 × Fin 2 → Fin 3 → Fin 3 → Fin 2 → Fin 2 → B
  /-- The colour stage. At fixed derivative, spinor and isospin indices the colour pair is
    classified, by the delta contraction if the block carries colour and trivially if it
    does not. -/
  colourStep : ∀ (q : Fin 1 ⊕ Fin 3) (l : Fin 2 × Fin 2) (w w' : Fin 2),
    InvariantReductionToSpan (fun U : specialUnitaryGroup (Fin 3) ℂ => repGauge (U, 1, 1))
      (Submodule.span ℂ (Set.range fun n : Fin 2 → Fin 3 => blk q l (n 0) (n 1) w w'))
  /-- The colour contraction lies in the span of the components it contracts. -/
  colourStep_mem : ∀ q l w w', (colourStep q l w w').spanningVector
    ∈ Submodule.span ℂ (Set.range fun n : Fin 2 → Fin 3 => blk q l (n 0) (n 1) w w')
  /-- The isospin stage, applied to the colour contraction. -/
  isospinStep : ∀ (q : Fin 1 ⊕ Fin 3) (l : Fin 2 × Fin 2),
    InvariantReductionToSpan (fun V : specialUnitaryGroup (Fin 2) ℂ => repGauge (1, V, 1))
      (Submodule.span ℂ
        (Set.range fun n : Fin 2 → Fin 2 => (colourStep q l (n 0) (n 1)).spanningVector))
  /-- The isospin contraction lies in the span of the colour contractions. -/
  isospinStep_mem : ∀ q l, (isospinStep q l).spanningVector
    ∈ Submodule.span ℂ
      (Set.range fun n : Fin 2 → Fin 2 => (colourStep q l (n 0) (n 1)).spanningVector)
  /-- The Lorentz stage, applied to the doubly contracted block, one four-vector index
    against a dual dotted and a dual undotted spinor index. -/
  lorentzStep : InvariantReductionToSpan (fun Λ : SL(2,ℂ) => repLorentz Λ)
    (Submodule.span ℂ (Set.range fun p : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2 =>
      (isospinStep p.1 p.2).spanningVector))
  /-- The Lorentz contraction lies in the span of the isospin contractions. -/
  lorentzStep_mem : lorentzStep.spanningVector
    ∈ Submodule.span ℂ (Set.range fun p : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2 =>
      (isospinStep p.1 p.2).spanningVector)
  /-- A hypercharge transformation fixes every component of the block, the hypercharges of
    a species and its conjugate cancelling. -/
  hyper : ∀ (t : unitary ℂ) q l c c' w w',
    repGauge ((1, 1, t) : GaugeGroupI) (blk q l c c' w w') = blk q l c c' w w'

namespace KineticBlock

variable {repGauge repLorentz} (K : KineticBlock repGauge repLorentz)

/-- The kinetic term of a block, the conjugate Pauli contraction of its doubly contracted
  form, which is `ψ̄ σ̄^μ ∂_μ ψ` with the colour and isospin indices already joined. -/
noncomputable def kineticTerm : B := K.lorentzStep.spanningVector

/-- The join, over the derivative, spinor and isospin indices, of the colour spans of the
  block, the span the block submodule is reduced from. -/
noncomputable def blockSpan : Submodule ℂ B :=
  ⨆ k : (Fin 1 ⊕ Fin 3) × (Fin 2 × Fin 2) × (Fin 2 × Fin 2),
    Submodule.span ℂ
      (Set.range fun n : Fin 2 → Fin 3 => K.blk k.1 k.2.1 (n 0) (n 1) k.2.2.1 k.2.2.2)

/-- The three stages in sequence. The block span reduces to the span of the kinetic term. -/
lemma reducesInvariantsTo :
    ReducesInvariantsTo (gaugeLorentzMaps repGauge repLorentz) K.blockSpan (ℂ ∙ K.kineticTerm) := by
  rw [blockSpan, kineticTerm]
  have hc := InvariantReductionToSpan.reducesInvariantsTo_iSup
    (σ := fun U : specialUnitaryGroup (Fin 3) ℂ => repGauge ((U, 1, 1) : GaugeGroupI))
    (V := fun k : (Fin 1 ⊕ Fin 3) × (Fin 2 × Fin 2) × (Fin 2 × Fin 2) =>
      Submodule.span ℂ
        (Set.range fun n : Fin 2 → Fin 3 => K.blk k.1 k.2.1 (n 0) (n 1) k.2.2.1 k.2.2.2))
    fun k => K.colourStep k.1 k.2.1 k.2.2.1 k.2.2.2
  have hi := InvariantReductionToSpan.reducesInvariantsTo_iSup
    (σ := fun V : specialUnitaryGroup (Fin 2) ℂ => repGauge ((1, V, 1) : GaugeGroupI))
    (V := fun p : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2 =>
      Submodule.span ℂ
        (Set.range fun n : Fin 2 → Fin 2 => (K.colourStep p.1 p.2 (n 0) (n 1)).spanningVector))
    fun p => K.isospinStep p.1 p.2
  have h1 := ReducesInvariantsTo.ofSU3 (repLorentz := repLorentz) hc
  have h2 := ReducesInvariantsTo.ofSU2 (repLorentz := repLorentz) hi
  have h3 := ReducesInvariantsTo.ofLorentz (repGauge := repGauge) K.lorentzStep.reducesInvariantsTo
  refine (h1.mono_right ?_).trans (h2.trans h3)
  refine Submodule.span_le.2 <| Set.range_subset_iff.2 fun k =>
    Submodule.mem_iSup_of_mem (k.1, k.2.1) (Submodule.subset_span ⟨![k.2.2.1, k.2.2.2], ?_⟩)
  simp

/-- The kinetic term lies in any submodule containing every component of the block, since each
  contraction lies in the span of the objects of the stage before it. -/
lemma kineticTerm_mem {V : Submodule ℂ B}
    (hV : ∀ q l c c' w w', K.blk q l c c' w w' ∈ V) : K.kineticTerm ∈ V := by
  have hcol : ∀ q l w w', (K.colourStep q l w w').spanningVector ∈ V := by
    intro q l w w'
    refine Submodule.span_le.2 ?_ (K.colourStep_mem q l w w')
    exact Set.range_subset_iff.2 fun n => hV q l (n 0) (n 1) w w'
  have hiso : ∀ q l, (K.isospinStep q l).spanningVector ∈ V := by
    intro q l
    refine Submodule.span_le.2 ?_ (K.isospinStep_mem q l)
    exact Set.range_subset_iff.2 fun n => hcol q l (n 0) (n 1)
  refine Submodule.span_le.2 ?_ K.lorentzStep_mem
  exact Set.range_subset_iff.2 fun p => hiso p.1 p.2

/-- The kinetic term is fixed by the colour factor, since the colour contractions are, and every
  later stage stays inside their span. -/
lemma repGauge_su3_kineticTerm (U : specialUnitaryGroup (Fin 3) ℂ) :
    repGauge ((U, 1, 1) : GaugeGroupI) K.kineticTerm = K.kineticTerm := by
  have hiso : ∀ p : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2, ∀ U',
      repGauge ((U', 1, 1) : GaugeGroupI) (K.isospinStep p.1 p.2).spanningVector
        = (K.isospinStep p.1 p.2).spanningVector := fun p U' =>
    isFixedBy_span_range
      (fun n U'' => (K.colourStep p.1 p.2 (n 0) (n 1)).spanningVector_fixed U'') U' _
      (K.isospinStep_mem p.1 p.2)
  exact isFixedBy_span_range (fun p U' => hiso p U') U _ K.lorentzStep_mem

/-- The kinetic term is fixed by the isospin factor. -/
lemma repGauge_su2_kineticTerm (V : specialUnitaryGroup (Fin 2) ℂ) :
    repGauge ((1, V, 1) : GaugeGroupI) K.kineticTerm = K.kineticTerm :=
  isFixedBy_span_range
    (fun p V' => (K.isospinStep p.1 p.2).spanningVector_fixed V') V _ K.lorentzStep_mem

/-- The kinetic term is fixed by the hypercharge factor, the hypercharges of a species and
  its conjugate cancelling on every component of the block. -/
lemma repGauge_u1_kineticTerm (t : unitary ℂ) :
    repGauge ((1, 1, t) : GaugeGroupI) K.kineticTerm = K.kineticTerm := by
  have hcol : ∀ q l w w', ∀ t' : unitary ℂ,
      repGauge ((1, 1, t') : GaugeGroupI) (K.colourStep q l w w').spanningVector
        = (K.colourStep q l w w').spanningVector := fun q l w w' t' =>
    isFixedBy_span_range (fun n t'' => K.hyper t'' q l (n 0) (n 1) w w') t' _
      (K.colourStep_mem q l w w')
  have hiso : ∀ p : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2, ∀ t' : unitary ℂ,
      repGauge ((1, 1, t') : GaugeGroupI) (K.isospinStep p.1 p.2).spanningVector
        = (K.isospinStep p.1 p.2).spanningVector := fun p t' =>
    isFixedBy_span_range (fun n t'' => hcol p.1 p.2 (n 0) (n 1) t'') t' _
      (K.isospinStep_mem p.1 p.2)
  exact isFixedBy_span_range (fun p t' => hiso p t') t _ K.lorentzStep_mem

/-- The kinetic term is gauge invariant. A gauge transformation is the product of its
  colour, isospin and hypercharge parts, and each fixes it. -/
lemma repGauge_kineticTerm (g : GaugeGroupI) : repGauge g K.kineticTerm = K.kineticTerm :=
  forall_repGauge_eq_self K.repGauge_su3_kineticTerm K.repGauge_su2_kineticTerm
    K.repGauge_u1_kineticTerm g

/-- The kinetic term is Lorentz invariant, being the conjugate Pauli contraction of a
  vector dual left-right Weyl family. -/
lemma repLorentz_kineticTerm (Λ : SL(2,ℂ)) :
    repLorentz Λ K.kineticTerm = K.kineticTerm := K.lorentzStep.spanningVector_fixed Λ

end KineticBlock

end Blocks

end FermionSector

end StandardModel
